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

/// The checkpoint slots. Two is the minimum, and more gives a rollback window: a
/// commit destroys exactly one checkpoint, the one in the slot it targets.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Geom {
    pub slots: Vec<Slot>,
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
        if self.slots.len() < 2 {
            return false;
        }
        for (i, x) in self.slots.iter().enumerate() {
            if x.payload.contains(&x.seal) {
                return false;
            }
            for (j, y) in self.slots.iter().enumerate() {
                if i == j {
                    continue;
                }
                if x.seal == y.seal
                    || x.payload.contains(&y.seal)
                    || !x.payload.is_disjoint(&y.payload)
                {
                    return false;
                }
            }
        }
        true
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

/// The slot whose generation strictly dominates every other.
///
/// A tie yields `None` on purpose. Two slots at one generation cannot arise from a
/// well-formed run, so a tie means the store is damaged — and there is nothing
/// underneath this layer to catch a wrong guess between two equally plausible
/// checkpoints.
pub fn live<'g>(g: &'g Geom, s: &Store) -> Option<&'g Slot> {
    let mut best: Option<(&Slot, u64)> = None;
    let mut tied = false;
    for sl in &g.slots {
        let Some(gn) = gen_at(s, sl.seal) else {
            continue;
        };
        match best {
            None => {
                best = Some((sl, gn));
                tied = false;
            }
            Some((_, b)) if gn > b => {
                best = Some((sl, gn));
                tied = false;
            }
            Some((_, b)) if gn == b => tied = true,
            Some(_) => {}
        }
    }
    if tied { None } else { best.map(|(sl, _)| sl) }
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

// ---------------------------------------------------------------------------
// Rung 2 — copy-on-write
// ---------------------------------------------------------------------------

/// A checkpoint that is in progress while the machine keeps running.
///
/// The whole design is one operator: the snapshot is `mem ◁ saved`, where `saved`
/// holds the contents a page had when the checkpoint began. `◁` gives the right
/// operand priority, so a page that has been written reads at its old contents.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Cow {
    /// What the machine reads and writes now.
    pub mem: Store,
    /// Contents copied aside, for pages written since the checkpoint began and not
    /// yet collected.
    pub saved: Delta,
    /// Pages already collected, at their start-of-checkpoint contents.
    pub out: Delta,
}

impl Cow {
    pub fn start(mem0: &Store) -> Cow {
        Cow {
            mem: mem0.clone(),
            saved: Delta::new(),
            out: Delta::new(),
        }
    }

    /// The snapshot the checkpoint writer sees.
    pub fn visible(&self) -> Store {
        override_(&self.mem, &self.saved)
    }

    /// The machine writes a page.
    ///
    /// `with_copy == false` models the third falsifiability gate: copy-on-write
    /// without the copy. The snapshot then follows the machine rather than holding
    /// still, and the checkpoint mixes two instants of memory.
    ///
    /// Never blocks. There is no condition on the progress of the checkpoint.
    pub fn mutate(&mut self, p: CellId, v: CellVal, with_copy: bool) {
        let needs_copy = with_copy && !self.out.contains_key(&p) && !self.saved.contains_key(&p);
        if let Some(old) = self.mem.get(&p).cloned().filter(|_| needs_copy) {
            self.saved.insert(p, old);
        }
        self.mem.insert(p, v);
    }

    /// The checkpoint writer collects a page.
    ///
    /// Releases the copy, which is what bounds the memory cost of a checkpoint: at
    /// most one copy per page, and only until the writer arrives. A second call for
    /// the same page does nothing, because by then the copy is gone and a re-read
    /// would take the current contents.
    ///
    /// Never blocks either.
    pub fn flush(&mut self, p: CellId) {
        if self.out.contains_key(&p) || !self.mem.contains_key(&p) {
            return;
        }
        let val = self.visible().get(&p).cloned().expect("page is in mem");
        self.saved.remove(&p);
        self.out.insert(p, val);
    }
}

// ---------------------------------------------------------------------------
// Rung 3 — capturing the state of a machine
// ---------------------------------------------------------------------------

pub type RegId = u64;

/// The state that persistence must preserve. Page tables live inside `mem`, like
/// any other data — capture works on physical cells and never translates an
/// address.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Machine {
    pub regs: BTreeMap<RegId, Vec<u8>>,
    pub mem: Store,
}

/// Where each part of the machine lives inside a slot.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Layout {
    pub cell_of: BTreeMap<RegId, CellId>,
    pub mem_cells: BTreeSet<CellId>,
}

impl Layout {
    pub fn reg_cells(&self) -> BTreeSet<CellId> {
        self.cell_of.values().copied().collect()
    }

    /// The register file and memory must not share a cell. A layout that overlaps
    /// loses state without a trace.
    pub fn wf(&self) -> bool {
        let regs = self.reg_cells();
        regs.len() == self.cell_of.len() && regs.is_disjoint(&self.mem_cells)
    }

    /// Every cell a capture writes.
    pub fn image(&self) -> BTreeSet<CellId> {
        self.reg_cells().union(&self.mem_cells).copied().collect()
    }
}

/// A machine, as a delta ready for a commit.
pub fn capture(lay: &Layout, m: &Machine) -> Delta {
    let mut d = Delta::new();
    // Memory first, then registers, so an overlapping layout shows the register
    // file winning — which is the fault the fourth gate is about.
    for (c, v) in &m.mem {
        if lay.mem_cells.contains(c) {
            d.insert(*c, v.clone());
        }
    }
    for (r, c) in &lay.cell_of {
        let w = m.regs.get(r).cloned().unwrap_or_default();
        d.insert(*c, CellVal::Data(w));
    }
    d
}

/// A machine, read back out of a store. Reads only the layout's own cells, so the
/// seal that recovery hands back is invisible.
pub fn restore(lay: &Layout, d: &Store) -> Machine {
    let regs = lay
        .cell_of
        .iter()
        .map(|(r, c)| {
            let w = match d.get(c) {
                Some(CellVal::Data(w)) => w.clone(),
                _ => Vec::new(),
            };
            (*r, w)
        })
        .collect();
    let mem = d
        .iter()
        .filter(|(c, _)| lay.mem_cells.contains(c))
        .map(|(c, v)| (*c, v.clone()))
        .collect();
    Machine { regs, mem }
}
