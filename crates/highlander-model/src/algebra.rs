//! §4 — The algebra: two monoids over one carrier.
//!
//! A [`Delta`] is a partial map from cell to value. Stores and deltas share a
//! carrier, which is what makes the algebra work at all.
//!
//! * `◁` ([`override_`]) sequences: right wins. Total, associative, **not** commutative.
//! * `•` ([`dunion`]) separates: defined only on disjoint domains. Associative,
//!   commutative, cancellative, unital — a separation algebra.
//!
//! # Why `•` is defined by hand instead of reusing `union_prefer_right`
//!
//! vstd's `Map::union_prefer_right` is exactly `◁`. Defining `•` as the same
//! function under a `disjoint` guard would make the bridge lemma ([`bridge`])
//! true by *reflexivity* — it would verify instantly and prove nothing, and §4.4,
//! §6.1 and §7.2 all lean on `•` carrying real weight.
//!
//! So `◁` prefers the **right** operand and `•` prefers the **left** one. The
//! bridge lemma then says exactly what it should: the bias is unobservable
//! precisely when the domains are disjoint.
//!
//! The guard rail for this is [`dunion_comm`]: it must not verify with its
//! `disjoint` precondition removed. If it does, the definitions have collapsed
//! into each other and the rest of the development is decoration.

use vstd::map::{assert_maps_equal, assert_maps_equal_internal};
use vstd::prelude::*;
use vstd::set_lib::{assert_sets_equal, assert_sets_equal_internal};

verus! {

broadcast use vstd::map_lib::group_map_properties;

/// Cells are opaque and independently replaceable. Not a byte offset, not a
/// sector number — §3.1 is deliberate about this. `nat` is just an index.
pub type CellId = nat;

/// A partial map from cell to value (§3.2).
pub type Delta<V> = Map<CellId, V>;

/// A store is a delta. Same carrier — that is the point (§3.2).
pub type Store<V> = Map<CellId, V>;

/// The unit of both monoids.
pub open spec fn unit<V>() -> Delta<V> {
    Map::empty()
}

/// `◁` — sequencing. Right wins (§4.1).
pub open spec fn override_<V>(s: Delta<V>, d: Delta<V>) -> Delta<V> {
    s.union_prefer_right(d)
}

/// The definedness side-condition of `•` (§4.2). Shows up three times across the
/// design: here, in epoch well-formedness (§6.1), and in the never-write-the-live-slot
/// rule (§7.5).
pub open spec fn disjoint<V>(a: Delta<V>, b: Delta<V>) -> bool {
    a.dom().disjoint(b.dom())
}

/// `•` — separation. **Left**-biased, deliberately; see the module docs.
///
/// Total as written, but only *meaningful* when [`disjoint`] holds. Verus has no
/// partial functions, so the partiality lives in the `recommends` clause and in
/// every caller's preconditions.
pub open spec fn dunion<V>(a: Delta<V>, b: Delta<V>) -> Delta<V>
    recommends
        disjoint(a, b),
{
    Map::new(
        a.dom().union(b.dom()),
        |k: CellId| if a.dom().contains(k) { a[k] } else { b[k] },
    )
}

// ---------------------------------------------------------------------------
// §4.1 — (Deltas, ◁, ∅) is a monoid
// ---------------------------------------------------------------------------

pub proof fn override_unit_left<V>(d: Delta<V>)
    ensures
        override_(unit::<V>(), d) =~= d,
{
    assert_maps_equal!(override_(unit::<V>(), d), d);
}

pub proof fn override_unit_right<V>(d: Delta<V>)
    ensures
        override_(d, unit::<V>()) =~= d,
{
    assert_maps_equal!(override_(d, unit::<V>()), d);
}

pub proof fn override_assoc<V>(a: Delta<V>, b: Delta<V>, c: Delta<V>)
    ensures
        override_(override_(a, b), c) =~= override_(a, override_(b, c)),
{
    assert_maps_equal!(override_(override_(a, b), c), override_(a, override_(b, c)));
}

/// §4.1 / §10 step 2: non-commutativity of `◁` as an **explicit counterexample**,
/// not a lemma. Returns the witnessing pair so the claim is externally visible
/// rather than buried in an `assert`.
pub proof fn override_not_commutative() -> (r: (Delta<u8>, Delta<u8>))
    ensures
        override_(r.0, r.1) != override_(r.1, r.0),
{
    let a: Delta<u8> = map![0nat => 1u8];
    let b: Delta<u8> = map![0nat => 2u8];
    assert(override_(a, b)[0nat] == 2u8);
    assert(override_(b, a)[0nat] == 1u8);
    (a, b)
}

// ---------------------------------------------------------------------------
// §4.2 — (Deltas, •, ∅) is a partial commutative monoid
// ---------------------------------------------------------------------------

pub proof fn dunion_unit_left<V>(d: Delta<V>)
    ensures
        dunion(unit::<V>(), d) =~= d,
{
    assert_maps_equal!(dunion(unit::<V>(), d), d);
}

pub proof fn dunion_unit_right<V>(d: Delta<V>)
    ensures
        dunion(d, unit::<V>()) =~= d,
{
    assert_maps_equal!(dunion(d, unit::<V>()), d);
}

/// Commutativity — **the guard rail**.
///
/// This is the lemma that decides whether `•` is a real separating conjunction or
/// a rename of `◁`. Because `dunion` is left-biased, `a • b` and `b • a` disagree
/// on any shared key, so the proof genuinely consumes `disjoint(a, b)`.
///
/// If you ever delete the `requires` clause and this still verifies, the
/// definitions are wrong. Stop and fix them before touching §7.
pub proof fn dunion_comm<V>(a: Delta<V>, b: Delta<V>)
    requires
        disjoint(a, b),
    ensures
        dunion(a, b) =~= dunion(b, a),
{
    assert_maps_equal!(dunion(a, b), dunion(b, a));
}

pub proof fn dunion_assoc<V>(a: Delta<V>, b: Delta<V>, c: Delta<V>)
    requires
        disjoint(a, b),
        disjoint(b, c),
        disjoint(a, c),
    ensures
        dunion(dunion(a, b), c) =~= dunion(a, dunion(b, c)),
{
    assert_maps_equal!(dunion(dunion(a, b), c), dunion(a, dunion(b, c)));
}

pub proof fn dunion_dom<V>(a: Delta<V>, b: Delta<V>)
    ensures
        dunion(a, b).dom() =~= a.dom().union(b.dom()),
{
    assert_sets_equal!(dunion(a, b).dom(), a.dom().union(b.dom()));
}

/// Cancellativity: `•` loses no information, which is what lets §6.2 recover an
/// epoch's individual writes from the assembled delta.
pub proof fn dunion_cancel<V>(a: Delta<V>, b: Delta<V>, c: Delta<V>)
    requires
        disjoint(a, b),
        disjoint(a, c),
        dunion(a, b) =~= dunion(a, c),
    ensures
        b =~= c,
{
    dunion_dom(a, b);
    dunion_dom(a, c);
    assert_maps_equal!(b, c, k => {
        if b.dom().contains(k) {
            assert(dunion(a, b).dom().contains(k));
            assert(!a.dom().contains(k));
            assert(dunion(a, b)[k] == b[k]);
        }
        if c.dom().contains(k) {
            assert(dunion(a, c).dom().contains(k));
            assert(!a.dom().contains(k));
            assert(dunion(a, c)[k] == c[k]);
        }
    });
}

// ---------------------------------------------------------------------------
// §4.3 — The bridge lemma
// ---------------------------------------------------------------------------

/// **Sequencing collapses into separation exactly when order stops mattering.**
///
/// Everything downstream leans on this. Note that it is a real proof obligation
/// only because `◁` and `•` disagree on their bias — see the module docs.
pub proof fn bridge<V>(a: Delta<V>, b: Delta<V>)
    requires
        disjoint(a, b),
    ensures
        override_(a, b) =~= dunion(a, b),
{
    assert_maps_equal!(override_(a, b), dunion(a, b));
}

/// The corollary §6.1 actually consumes: within an epoch, order is unobservable,
/// which is what licenses modelling epoch assembly with `•` instead of `◁`.
pub proof fn override_comm_when_disjoint<V>(a: Delta<V>, b: Delta<V>)
    requires
        disjoint(a, b),
    ensures
        override_(a, b) =~= override_(b, a),
{
    bridge(a, b);
    bridge(b, a);
    dunion_comm(a, b);
}

} // verus!
