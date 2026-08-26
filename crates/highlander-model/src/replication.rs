//! Rung 6 — replication across nodes.
//!
//! Rungs 1 to 5 make one machine survive its own crash. Every axiom they rest on is
//! a promise about **one device**: A1 and A2 describe how a single store behaves
//! when power fails. Rung 6 does not extend that model — it replaces the failure
//! model, because a partition is not a fault A1 or A2 describes.
//!
//! **This is the first rung that is not finished.** Safety is proven below;
//! liveness is not attempted, and for a cluster that is half the design rather than
//! a footnote. The design doc's ladder marks it `◐` for exactly that reason.
//!
//! # What actually changes
//!
//! Below this module, `protocol::live` is a *function of the store*. One reader
//! examines every slot and returns an answer, and `at_most_one_live_slot` is a
//! consequence rather than an agreement. That is why N slots needed no protocol:
//! slots on one device cannot disagree, because nothing ever reads a subset of them.
//!
//! Replicas can. A node sees its own store and whatever it can reach, and it cannot
//! distinguish a peer that is slow from a peer that is gone. No node holds the whole
//! picture, so *which checkpoint is authoritative* stops being a lookup and becomes
//! a question that a group has to answer together.
//!
//! # What this module proves, and what it does not
//!
//! Everything here rests on one combinatorial fact: **any two majorities of a set
//! share a member** ([`quorums_intersect`]). That single fact gives:
//!
//! * [`agreement`] — one generation has one checkpoint, whatever any node believes;
//! * [`a_committed_checkpoint_reaches_every_quorum`] — a committed checkpoint is
//!   visible to every future quorum, so it cannot be lost by electing a new leader.
//!
//! Those are the safety properties of consensus. They are stated over the *state* a
//! protocol maintains, and not over a protocol. Nothing here runs an election,
//! counts a vote or sends a heartbeat.
//!
//! **Liveness is out of scope, and it is the hard half in practice.** A partition
//! can stop progress for as long as it lasts, and no amount of safety prevents that.
//! Proving that a protocol *makes* progress needs a partial-synchrony model, which
//! is a different piece of work with different assumptions.
//!
//! # How this layers on the rungs
//!
//! Rung 1 says a node's checkpoint does not tear. This module says which non-torn
//! checkpoint is authoritative. They answer different questions, and each node in a
//! cluster runs the whole of rungs 1 to 5 locally.

use vstd::prelude::*;
use vstd::set_lib::{assert_sets_equal, assert_sets_equal_internal};
#[cfg(verus_only)]
use vstd::set_lib::{lemma_len_subset, lemma_set_intersect_union_lens};

use crate::algebra::Delta;
use crate::protocol::CellVal;

verus! {

pub type NodeId = nat;

/// The machines holding replicas. Fixed membership — reconfiguration is its own
/// problem and its own proof.
pub struct Cluster {
    pub nodes: Set<NodeId>,
}

/// A group large enough to decide: strictly more than half.
///
/// The strictness is the whole thing. `>=` would admit two disjoint halves of an
/// even cluster, and the `half-quorums` gate shows exactly what that costs.
#[cfg(not(feature = "half-quorums"))]
pub open spec fn is_quorum(c: Cluster, q: Set<NodeId>) -> bool {
    &&& q.subset_of(c.nodes)
    &&& 2 * q.len() > c.nodes.len()
}

/// **The eighth falsifiability gate (`--features half-quorums`).**
///
/// Accepts exactly half a cluster as a quorum. Two disjoint halves of an even
/// cluster are then both quorums, they share no node, and two different checkpoints
/// can be committed at one generation. `quorums_intersect` must fail with this
/// feature on.
#[cfg(feature = "half-quorums")]
pub open spec fn is_quorum(c: Cluster, q: Set<NodeId>) -> bool {
    &&& q.subset_of(c.nodes)
    &&& 2 * q.len() >= c.nodes.len()
}

/// **The one fact everything rests on: two quorums share a node.**
///
/// `|q1| + |q2| > |nodes| >= |q1 ∪ q2|`, and inclusion-exclusion turns that into
/// `|q1 ∩ q2| > 0`. No protocol, no messages — just counting.
pub proof fn quorums_intersect(c: Cluster, q1: Set<NodeId>, q2: Set<NodeId>) -> (nd: NodeId)
    requires
        is_quorum(c, q1),
        is_quorum(c, q2),
    ensures
        q1.contains(nd),
        q2.contains(nd),
{
    lemma_set_intersect_union_lens(q1, q2);
    assert(q1.union(q2).subset_of(c.nodes)) by {
        assert_sets_equal!(q1 + q2, q1.union(q2));
    }
    lemma_len_subset(q1 + q2, c.nodes);

    let shared = q1.intersect(q2);
    assert(shared.len() > 0);
    assert(exists|x: NodeId| shared.contains(x)) by {
        if forall|x: NodeId| !shared.contains(x) {
            assert_sets_equal!(shared, Set::<NodeId>::empty());
        }
    }
    let nd = shared.choose();
    assert(shared.contains(nd));
    nd
}

// ---------------------------------------------------------------------------
// What a cluster holds
// ---------------------------------------------------------------------------

/// What one node has sealed: a generation, and the checkpoint it names.
///
/// `None` means the node has never sealed anything.
pub type NodeState = Option<(nat, Delta<CellVal>)>;

pub type ClusterState = Map<NodeId, NodeState>;

pub open spec fn holds(st: ClusterState, nd: NodeId, generation: nat, image: Delta<CellVal>) -> bool {
    &&& st.dom().contains(nd)
    &&& st[nd] == Some((generation, image))
}

/// **The obligation a protocol must meet.**
///
/// A node never seals two different checkpoints at one generation. This is not
/// proven here — it is what the writing side has to guarantee, and it is the reason
/// a generation number is allocated once rather than reused.
///
/// A3 does the same job it has done since rung 1: generations are totally ordered
/// and never repeat.
pub open spec fn nodes_are_consistent(st: ClusterState) -> bool {
    forall|nd: NodeId, g1: nat, i1: Delta<CellVal>, i2: Delta<CellVal>|
        #![trigger holds(st, nd, g1, i1), holds(st, nd, g1, i2)]
        holds(st, nd, g1, i1) && holds(st, nd, g1, i2) ==> i1 == i2
}

/// A checkpoint is committed when a quorum holds it.
///
/// Not "when the leader wrote it", and not "when one node acknowledged it". A quorum
/// is the smallest group whose agreement cannot be contradicted by another group.
pub open spec fn committed(
    c: Cluster,
    st: ClusterState,
    generation: nat,
    image: Delta<CellVal>,
) -> bool {
    exists|q: Set<NodeId>|
        #![trigger is_quorum(c, q)]
        is_quorum(c, q) && forall|nd: NodeId| q.contains(nd) ==> holds(st, nd, generation, image)
}

// ---------------------------------------------------------------------------
// Safety
// ---------------------------------------------------------------------------

/// **Agreement: one generation, one checkpoint.**
///
/// Two quorums cannot commit different checkpoints at the same generation, because
/// they share a node and that node holds only one.
///
/// This is what a single-device store gets for free — `at_most_one_live_slot` is the
/// same statement, proven by reading every slot. Across a cluster nobody can read
/// every replica, so the property has to come from counting instead.
pub proof fn agreement(
    c: Cluster,
    st: ClusterState,
    generation: nat,
    i1: Delta<CellVal>,
    i2: Delta<CellVal>,
)
    requires
        nodes_are_consistent(st),
        committed(c, st, generation, i1),
        committed(c, st, generation, i2),
    ensures
        i1 == i2,
{
    let q1 = choose|q: Set<NodeId>|
        is_quorum(c, q) && forall|nd: NodeId| q.contains(nd) ==> holds(st, nd, generation, i1);
    let q2 = choose|q: Set<NodeId>|
        is_quorum(c, q) && forall|nd: NodeId| q.contains(nd) ==> holds(st, nd, generation, i2);

    let nd = quorums_intersect(c, q1, q2);
    assert(holds(st, nd, generation, i1));
    assert(holds(st, nd, generation, i2));
}

/// **A committed checkpoint reaches every quorum.**
///
/// Whatever group next assembles, it contains a node that already holds the
/// committed checkpoint. A new leader therefore cannot be elected in ignorance of
/// it, which is why a commit survives the loss of any minority.
///
/// This is Raft's *leader completeness*, reduced to the counting argument it
/// actually is.
pub proof fn a_committed_checkpoint_reaches_every_quorum(
    c: Cluster,
    st: ClusterState,
    generation: nat,
    image: Delta<CellVal>,
    q: Set<NodeId>,
) -> (nd: NodeId)
    requires
        committed(c, st, generation, image),
        is_quorum(c, q),
    ensures
        q.contains(nd),
        holds(st, nd, generation, image),
{
    let qc = choose|x: Set<NodeId>|
        is_quorum(c, x) && forall|nd: NodeId| x.contains(nd) ==> holds(st, nd, generation, image);
    let nd = quorums_intersect(c, qc, q);
    nd
}

/// **A single node's view is not authoritative.**
///
/// Node 0 holds generation 5 and believes it is current. Generation 6 is committed
/// by a quorum that does not include node 0. The node is not faulty and its store is
/// not torn — rung 1 holds perfectly — and it is still wrong about which checkpoint
/// is live.
///
/// This is the exact thing `protocol::live` cannot do once replicas exist, and the
/// reason replication is not another rung.
pub proof fn a_local_view_can_be_stale(older: Delta<CellVal>, newer: Delta<CellVal>) -> (r: (
    Cluster,
    ClusterState,
))
    ensures
        holds(r.1, 0, 5, older),
        committed(r.0, r.1, 6, newer),
        !holds(r.1, 0, 6, newer),
{
    let c = Cluster { nodes: set![0nat, 1nat, 2nat] };
    let st: ClusterState = map![
        0nat => Some((5nat, older)),
        1nat => Some((6nat, newer)),
        2nat => Some((6nat, newer))
    ];
    let q = set![1nat, 2nat];

    assert(c.nodes.len() == 3);
    assert(q.len() == 2);
    assert(is_quorum(c, q));
    assert(forall|nd: NodeId| q.contains(nd) ==> holds(st, nd, 6nat, newer));
    assert(committed(c, st, 6nat, newer));
    (c, st)
}

// ---------------------------------------------------------------------------
// Across generations: what an election must not lose
// ---------------------------------------------------------------------------

/// The generation a node has sealed. `-1` means it has sealed nothing, which ranks
/// below every real generation — the same convention `protocol::gen_below` uses for
/// an absent seal.
pub open spec fn gen_of(st: ClusterState, nd: NodeId) -> int {
    if st.dom().contains(nd) {
        match st[nd] {
            Some((g, _)) => g as int,
            None => -1,
        }
    } else {
        -1
    }
}

pub proof fn holding_fixes_the_generation(
    st: ClusterState,
    nd: NodeId,
    generation: nat,
    image: Delta<CellVal>,
)
    requires
        holds(st, nd, generation, image),
    ensures
        gen_of(st, nd) == generation as int,
{
}

/// A candidate may lead when a quorum votes for it **and no voter is ahead of it**.
///
/// The second clause is the whole of leader completeness. Raft states it as "vote
/// only for a candidate at least as up to date as you", and without it a node that
/// missed a commit can be elected and then overwrite it.
#[cfg(not(feature = "elect-any-node"))]
pub open spec fn electable(
    c: Cluster,
    st: ClusterState,
    cand: NodeId,
    q: Set<NodeId>,
) -> bool {
    &&& is_quorum(c, q)
    &&& forall|nd: NodeId| #![auto] q.contains(nd) ==> gen_of(st, nd) <= gen_of(st, cand)
}

/// **The ninth falsifiability gate (`--features elect-any-node`).**
///
/// Drops the up-to-date rule, so a quorum may elect any candidate. A node that
/// missed a committed checkpoint can then lead, and the next commit it makes is
/// derived from a state older than one already committed — the committed checkpoint
/// is lost. `an_electable_leader_has_seen_every_commit` must fail with this feature
/// on.
#[cfg(feature = "elect-any-node")]
pub open spec fn electable(
    c: Cluster,
    st: ClusterState,
    cand: NodeId,
    q: Set<NodeId>,
) -> bool {
    is_quorum(c, q)
}

/// **Leader completeness: an electable leader has seen every committed checkpoint.**
///
/// The voting quorum and the committing quorum share a node. That node holds the
/// committed generation, and no voter is ahead of the candidate, so the candidate is
/// at least as far along as the commit. It cannot lead in ignorance of it.
///
/// This is the property that makes a commit *final*. `agreement` says one generation
/// has one checkpoint; this says a later leader cannot quietly discard it.
pub proof fn an_electable_leader_has_seen_every_commit(
    c: Cluster,
    st: ClusterState,
    cand: NodeId,
    q: Set<NodeId>,
    generation: nat,
    image: Delta<CellVal>,
)
    requires
        electable(c, st, cand, q),
        committed(c, st, generation, image),
    ensures
        gen_of(st, cand) >= generation as int,
{
    let qc = choose|x: Set<NodeId>|
        is_quorum(c, x) && forall|nd: NodeId| x.contains(nd) ==> holds(st, nd, generation, image);
    let nd = quorums_intersect(c, qc, q);
    assert(holds(st, nd, generation, image));
    holding_fixes_the_generation(st, nd, generation, image);
    assert(gen_of(st, nd) <= gen_of(st, cand));
}

/// **What the up-to-date rule is for.**
///
/// 5 nodes. Generation 6 is committed by `{1,2,3}`. Node 0 never received it and
/// still holds generation 5. The group `{0,3,4}` is a perfectly good quorum, and it
/// contains node 0 — so a rule that only counted votes would elect a leader that had
/// never seen generation 6, and its next commit would erase it.
///
/// The up-to-date rule rejects node 0, because node 3 is in that quorum and node 3
/// is ahead of it. The counterexample is why the rule exists, and the last clause is
/// what the `elect-any-node` gate removes.
pub proof fn the_up_to_date_rule_rejects_a_stale_candidate(
    older: Delta<CellVal>,
    newer: Delta<CellVal>,
) -> (r: (Cluster, ClusterState, Set<NodeId>))
    ensures
        committed(r.0, r.1, 6, newer),
        is_quorum(r.0, r.2),
        r.2.contains(0),
        gen_of(r.1, 0) < 6,
        !electable(r.0, r.1, 0, r.2),
{
    let c = Cluster { nodes: set![0nat, 1nat, 2nat, 3nat, 4nat] };
    let st: ClusterState = map![
        0nat => Some((5nat, older)),
        1nat => Some((6nat, newer)),
        2nat => Some((6nat, newer)),
        3nat => Some((6nat, newer)),
        4nat => Some((5nat, older))
    ];

    assert(c.nodes.len() == 5);

    // Generation 6 is committed: nodes 1, 2 and 3 are a majority and all hold it.
    let qc = set![1nat, 2nat, 3nat];
    assert(qc.len() == 3);
    assert(is_quorum(c, qc));
    assert(forall|nd: NodeId| qc.contains(nd) ==> holds(st, nd, 6nat, newer));
    assert(committed(c, st, 6nat, newer));

    // And this quorum would have elected node 0, had votes been all that counted.
    let q = set![0nat, 3nat, 4nat];
    assert(q.len() == 3);
    assert(is_quorum(c, q));
    assert(gen_of(st, 0) == 5);
    assert(gen_of(st, 3) == 6);

    // Node 3 is in that quorum and is ahead of node 0, so the rule refuses.
    assert(q.contains(3nat));
    assert(!(gen_of(st, 3nat) <= gen_of(st, 0nat)));
    assert(!electable(c, st, 0, q));
    (c, st, q)
}

} // verus!
