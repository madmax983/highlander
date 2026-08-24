//! An executable reference implementation of the highlander checkpoint protocol.
//!
//! # Why this exists
//!
//! The proof checks the model against itself. It cannot tell you that the model
//! describes a machine — that an epoch decomposition means what it should, that
//! `recover` picks the slot a real implementation would pick, that the commit
//! sequence is the one you would actually issue to a device.
//!
//! This module is a second, independent expression of the same protocol in ordinary
//! Rust, and `tests/proptest_crash.rs` hammers it with random payloads and random
//! landing schedules. When the two disagree, one of them is wrong — and it is worth
//! knowing which before rung 2 is built on top.
//!
//! Deliberately dumb: `BTreeMap`, no cleverness. It is a **separate crate** and does
//! not depend on `highlander-model` at all — a reference implementation that shared
//! code with the specification it is meant to cross-check would be worthless.

#![no_std]

extern crate alloc;

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec::Vec;

pub type CellId = u64;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum CellVal {
    Data(Vec<u8>),
    Seal { generation: u64, crc: u64 },
}

pub type Store = BTreeMap<CellId, CellVal>;
/// A delta is the same carrier as a store — §3.2, and the reason the algebra works.
pub type Delta = BTreeMap<CellId, CellVal>;

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Slot {
    pub seal: CellId,
    pub payload: BTreeSet<CellId>,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Geom {
    pub a: Slot,
    pub b: Slot,
}

impl Slot {
    /// Everything the slot owns: payload plus seal.
    pub fn footprint(&self) -> BTreeSet<CellId> {
        let mut f = self.payload.clone();
        f.insert(self.seal);
        f
    }
}

impl Geom {
    pub fn slots_wf(&self) -> bool {
        self.a.seal != self.b.seal
            && !self.a.payload.contains(&self.a.seal)
            && !self.b.payload.contains(&self.b.seal)
            && !self.a.payload.contains(&self.b.seal)
            && !self.b.payload.contains(&self.a.seal)
            && self.a.payload.is_disjoint(&self.b.payload)
    }

    pub fn other<'g>(&'g self, sl: &Slot) -> &'g Slot {
        if sl == &self.a { &self.b } else { &self.a }
    }
}

/// `◁` — sequencing. Right wins (§4.1).
pub fn override_(s: &Store, d: &Delta) -> Store {
    let mut out = s.clone();
    for (k, v) in d {
        out.insert(*k, v.clone());
    }
    out
}

/// `•` — separation. Returns `None` when the domains overlap, which is the
/// definedness side-condition of §4.2 rather than an error case.
pub fn dunion(a: &Delta, b: &Delta) -> Option<Delta> {
    if a.keys().any(|k| b.contains_key(k)) {
        return None;
    }
    let mut out = a.clone();
    for (k, v) in b {
        out.insert(*k, v.clone());
    }
    Some(out)
}

/// No CRC check — see `protocol`'s module docs for why that is deliberate.
pub fn gen_at(s: &Store, c: CellId) -> Option<u64> {
    match s.get(&c) {
        Some(CellVal::Seal { generation, .. }) => Some(*generation),
        _ => None,
    }
}

pub fn live<'g>(g: &'g Geom, s: &Store) -> Option<&'g Slot> {
    match (gen_at(s, g.a.seal), gen_at(s, g.b.seal)) {
        (None, None) => None,
        (Some(_), None) => Some(&g.a),
        (None, Some(_)) => Some(&g.b),
        (Some(x), Some(y)) => {
            if x >= y {
                Some(&g.a)
            } else {
                Some(&g.b)
            }
        }
    }
}

/// §7.5 — projection onto the live checkpoint. Never writes.
pub fn recover(g: &Geom, s: &Store) -> Store {
    match live(g, s) {
        None => Store::new(),
        Some(sl) => {
            let f = sl.footprint();
            s.iter()
                .filter(|(k, _)| f.contains(k))
                .map(|(k, v)| (*k, v.clone()))
                .collect()
        }
    }
}

pub fn clean(g: &Geom, s: &Store) -> bool {
    &recover(g, s) == s
}

/// The commit, as its epoch decomposition: payload, then seal.
///
/// `with_barrier == false` models the broken protocol the falsifiability gate
/// describes — the two epochs merge into one, and the property test should then be
/// able to find a state that recovers to neither generation.
pub fn commit_epochs(
    payload: &[(CellId, Vec<u8>)],
    target: &Slot,
    n: u64,
    crc: u64,
    with_barrier: bool,
) -> Vec<Delta> {
    let mut e_payload = Delta::new();
    for (c, bytes) in payload {
        e_payload.insert(*c, CellVal::Data(bytes.clone()));
    }
    let mut e_seal = Delta::new();
    e_seal.insert(
        target.seal,
        CellVal::Seal {
            generation: n + 1,
            crc,
        },
    );

    if with_barrier {
        alloc::vec![e_payload, e_seal]
    } else {
        // No barrier: one epoch, so a crash can land the seal without the payload.
        let merged = dunion(&e_payload, &e_seal).expect("seal cell is outside the payload region");
        alloc::vec![merged]
    }
}

/// Sequence every epoch onto the store — the uninterrupted run.
pub fn denote(s0: &Store, epochs: &[Delta]) -> Store {
    let mut s = s0.clone();
    for e in epochs {
        s = override_(&s, e);
    }
    s
}

/// A crash during epoch `k` in which exactly the cells in `landed` made it.
///
/// `landed` is an arbitrary subset — not a prefix. Real devices reorder freely
/// between barriers (§6.2), and testing only prefixes would test a machine nobody
/// owns.
pub fn crash_at(s0: &Store, epochs: &[Delta], k: usize, landed: &BTreeSet<CellId>) -> Store {
    let mut s = s0.clone();
    for e in epochs.iter().take(k) {
        s = override_(&s, e);
    }
    let sigma: Delta = epochs[k]
        .iter()
        .filter(|(c, _)| landed.contains(c))
        .map(|(c, v)| (*c, v.clone()))
        .collect();
    override_(&s, &sigma)
}
