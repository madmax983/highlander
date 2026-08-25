//! Rung 3 — capturing the state of a real machine.
//!
//! Rungs 1 and 2 move *cells*. They never ask what a cell means. Rung 3 asks: the
//! thing being checkpointed is a machine, with registers and page tables, and the
//! checkpoint must hold all of it. If capture loses anything, rung 4 cannot resume,
//! and every result below this point describes a checkpoint of nothing in
//! particular.
//!
//! The theorem is [`capture_restore_roundtrip`]: capture followed by restore is the
//! identity on machines. The checkpoint is **lossless**.
//!
//! # Page tables are ordinary memory
//!
//! A page table is data in cells, and [`capture`] treats it as such. This is a
//! design decision and not an omission: capture works on *physical* cells, so it
//! never translates an address. The alternative — capturing virtual memory — needs
//! the page tables in order to read the page tables, which is a circularity with no
//! base case. [`page_tables_are_ordinary_memory`] states the consequence.
//!
//! # The mechanism boundary
//!
//! §8 of the design doc records the boundary at the outside of the machine: the
//! world does not go back to an earlier state. There is a second boundary, at the
//! inside, and the design doc does not mention it.
//!
//! The checkpoint machinery is itself part of the machine. Its seal cells, and the
//! registers its writer uses, are state. If the capture includes them, then the
//! capture must describe itself, and the regress has no base case. So it does not
//! include them: [`mechanism_cells`] are outside every layout, and
//! [`capture_excludes_the_mechanism`] proves the capture never touches them.
//!
//! Thus persistence is orthogonal **for the machine**, and not for the mechanism.
//! The mechanism is re-derived on resume from the seal, and it is not restored.
//! [`restore_ignores_the_mechanism`] is the statement that makes this safe: a
//! restore reads only the layout's own cells, so the seal that recovery hands back
//! is invisible to it.

use vstd::map::{assert_maps_equal, assert_maps_equal_internal};
use vstd::prelude::*;
use vstd::set_lib::{assert_sets_equal, assert_sets_equal_internal};

use crate::algebra::{CellId, Delta};
#[cfg(verus_only)]
use crate::algebra::{disjoint, dunion, override_, unit};
use crate::protocol::{CellVal, Geom};

verus! {

broadcast use vstd::map_lib::group_map_properties;

pub type RegId = nat;

/// A register holds bytes, exactly as a cell does. Nothing here needs a width.
pub type Word = Seq<u8>;

/// The state that persistence must preserve.
///
/// `mem` is physical memory. Page tables live inside it, like any other data.
pub struct Machine {
    pub regs: Map<RegId, Word>,
    pub mem: Delta<CellVal>,
}

/// Where each part of the machine lives inside a slot.
///
/// The two register maps are inverse to each other. Storing both directions avoids
/// a `choose` in every definition, and it states the bijection openly rather than
/// deriving it.
pub struct Layout {
    /// Which cell holds a given register.
    pub cell_of: Map<RegId, CellId>,
    /// Which register a given cell holds.
    pub reg_of: Map<CellId, RegId>,
    /// The cells that hold physical memory.
    pub mem_cells: Set<CellId>,
}

/// Every cell a capture writes.
pub open spec fn image(lay: Layout) -> Set<CellId> {
    lay.reg_of.dom().union(lay.mem_cells)
}

/// The register file and memory must not share a cell.
///
/// **This is the definedness condition of `•` for the fourth time.** §4.4 counts
/// three appearances; rung 3 adds one more. A layout that overlaps loses data
/// silently, which is what the `overlapping-layout` gate demonstrates.
pub open spec fn layout_wf(lay: Layout) -> bool {
    &&& forall|r: RegId| #![auto]
        lay.cell_of.dom().contains(r) ==> lay.reg_of.dom().contains(lay.cell_of[r])
            && lay.reg_of[lay.cell_of[r]] == r
    &&& forall|c: CellId| #![auto]
        lay.reg_of.dom().contains(c) ==> lay.cell_of.dom().contains(lay.reg_of[c])
            && lay.cell_of[lay.reg_of[c]] == c
    &&& reg_cells_disjoint_from_memory(lay)
}

#[cfg(not(feature = "overlapping-layout"))]
pub open spec fn reg_cells_disjoint_from_memory(lay: Layout) -> bool {
    lay.reg_of.dom().disjoint(lay.mem_cells)
}

/// **The fourth falsifiability gate (`--features overlapping-layout`).**
///
/// Drops the requirement that the register file and memory occupy different cells.
/// A capture then writes both to the same cell, one of them wins, and the other is
/// lost without a trace. `capture_restore_roundtrip` must fail with this feature on.
#[cfg(feature = "overlapping-layout")]
pub open spec fn reg_cells_disjoint_from_memory(lay: Layout) -> bool {
    true
}

/// The machine and the layout describe the same registers and the same memory.
pub open spec fn machine_fits(lay: Layout, m: Machine) -> bool {
    &&& layout_wf(lay)
    &&& lay.cell_of.dom() =~= m.regs.dom()
    &&& m.mem.dom() =~= lay.mem_cells
}

// ---------------------------------------------------------------------------
// Capture and restore
// ---------------------------------------------------------------------------

/// The register file, as cells.
pub open spec fn reg_image(lay: Layout, m: Machine) -> Delta<CellVal> {
    Map::new(lay.reg_of.dom(), |c: CellId| CellVal::Data(m.regs[lay.reg_of[c]]))
}

/// A machine, as a delta ready for a commit.
///
/// Assembled with `•`, not `◁`: the register file and memory are separate regions,
/// and the algebra records that rather than letting one quietly overwrite the other.
pub open spec fn capture(lay: Layout, m: Machine) -> Delta<CellVal> {
    dunion(reg_image(lay, m), m.mem)
}

pub open spec fn word_at(d: Delta<CellVal>, c: CellId) -> Word {
    match d[c] {
        CellVal::Data(w) => w,
        CellVal::Seal { generation: _, crc: _ } => Seq::empty(),
    }
}

/// A machine, read back out of a store.
///
/// Reads only the layout's own cells. Anything else in the store — the seal that
/// recovery hands back, the other slot — is invisible.
pub open spec fn restore(lay: Layout, d: Delta<CellVal>) -> Machine {
    Machine {
        regs: Map::new(lay.cell_of.dom(), |r: RegId| word_at(d, lay.cell_of[r])),
        mem: d.restrict(lay.mem_cells),
    }
}

/// **Memory survives the capture.**
///
/// The register file does not overwrite memory. Stated cell by cell, because that
/// is the form that needs no proof at all when the layout is sound, and becomes
/// false immediately when it is not.
///
/// This is the target of the `overlapping-layout` gate.
pub proof fn capture_preserves_memory_at(lay: Layout, m: Machine, c: CellId)
    requires
        machine_fits(lay, m),
        m.mem.dom().contains(c),
    ensures
        capture(lay, m)[c] == m.mem[c],
{
}

pub proof fn capture_dom(lay: Layout, m: Machine)
    requires
        machine_fits(lay, m),
    ensures
        capture(lay, m).dom() =~= image(lay),
{
    crate::algebra::dunion_dom(reg_image(lay, m), m.mem);
}

/// **The rung 3 theorem: the checkpoint is lossless.**
///
/// Capture followed by restore is the identity. Nothing about the machine is
/// dropped, reordered or approximated on the way into a checkpoint.
pub proof fn capture_restore_roundtrip(lay: Layout, m: Machine)
    requires
        machine_fits(lay, m),
    ensures
        restore(lay, capture(lay, m)).regs =~= m.regs,
        restore(lay, capture(lay, m)).mem =~= m.mem,
        restore(lay, capture(lay, m)) == m,
{
    let d = capture(lay, m);
    crate::algebra::dunion_dom(reg_image(lay, m), m.mem);

    assert_maps_equal!(restore(lay, d).regs, m.regs, r => {
        if m.regs.dom().contains(r) {
            let c = lay.cell_of[r];
            assert(lay.reg_of.dom().contains(c));
            assert(lay.reg_of[c] == r);
            assert(!m.mem.dom().contains(c));
            assert(d[c] == CellVal::Data(m.regs[r]));
        }
    });

    assert_maps_equal!(restore(lay, d).mem, m.mem, c => {
        if m.mem.dom().contains(c) {
            assert(!lay.reg_of.dom().contains(c));
        }
    });

    assert(restore(lay, d).regs == m.regs);
    assert(restore(lay, d).mem == m.mem);
}

/// A page table is data in cells, so it survives like any other data. There is no
/// separate mechanism, and there is no address translation anywhere in this module.
pub proof fn page_tables_are_ordinary_memory(lay: Layout, m: Machine, pt: Set<CellId>)
    requires
        machine_fits(lay, m),
        pt.subset_of(lay.mem_cells),
    ensures
        restore(lay, capture(lay, m)).mem.restrict(pt) =~= m.mem.restrict(pt),
{
    capture_restore_roundtrip(lay, m);
}

// ---------------------------------------------------------------------------
// The mechanism boundary
// ---------------------------------------------------------------------------

/// The cells the checkpoint machinery owns. They are not part of any machine.
pub open spec fn mechanism_cells(g: Geom) -> Set<CellId> {
    g.slots.map_values(|sl: crate::protocol::Slot| sl.seal).to_set()
}

pub open spec fn machine_outside_mechanism(lay: Layout, g: Geom) -> bool {
    image(lay).disjoint(mechanism_cells(g))
}

/// The capture never writes the machinery's own cells, so it does not have to
/// describe itself.
pub proof fn capture_excludes_the_mechanism(lay: Layout, m: Machine, g: Geom)
    requires
        machine_fits(lay, m),
        machine_outside_mechanism(lay, g),
    ensures
        capture(lay, m).dom().disjoint(mechanism_cells(g)),
{
    capture_dom(lay, m);
}

/// **No layout can put the capture inside the memory it captures.**
///
/// The boundary is not a convention. Suppose the capture landed entirely within the
/// cells it is capturing. The register file is part of the capture, and a register
/// cell is not a memory cell, so the capture reaches outside the memory — always,
/// for any machine with at least one register.
///
/// The obstruction is arithmetic, and not logic. A container of a fixed size cannot
/// hold a faithful copy of itself **and** anything else, and
/// `capture_restore_roundtrip` is exactly the statement that the copy is faithful.
/// Losslessness and total self-inclusion are not compatible, thus proving the first
/// removes the second.
pub proof fn no_layout_captures_itself(lay: Layout, m: Machine, r: RegId)
    requires
        machine_fits(lay, m),
        lay.cell_of.dom().contains(r),
    ensures
        !image(lay).subset_of(lay.mem_cells),
{
    let c = lay.cell_of[r];
    assert(lay.reg_of.dom().contains(c));
    assert(image(lay).contains(c));
    assert(!lay.mem_cells.contains(c));
}

/// A restore reads only the layout's cells, so whatever the machinery leaves in the
/// store is invisible to it. This is what lets recovery hand back a slot that
/// contains a seal.
pub proof fn restore_ignores_the_mechanism(lay: Layout, d1: Delta<CellVal>, d2: Delta<CellVal>)
    requires
        layout_wf(lay),
        image(lay).subset_of(d1.dom()),
        image(lay).subset_of(d2.dom()),
        d1.restrict(image(lay)) =~= d2.restrict(image(lay)),
    ensures
        restore(lay, d1).regs =~= restore(lay, d2).regs,
        restore(lay, d1).mem =~= restore(lay, d2).mem,
{
    let r1 = d1.restrict(image(lay));
    let r2 = d2.restrict(image(lay));

    assert_maps_equal!(restore(lay, d1).regs, restore(lay, d2).regs, r => {
        if lay.cell_of.dom().contains(r) {
            let c = lay.cell_of[r];
            assert(image(lay).contains(c));
            assert(r1[c] == d1[c]);
            assert(r2[c] == d2[c]);
        }
    });

    assert_maps_equal!(restore(lay, d1).mem, restore(lay, d2).mem, c => {
        if lay.mem_cells.contains(c) {
            assert(image(lay).contains(c));
            assert(r1[c] == d1[c]);
            assert(r2[c] == d2[c]);
        }
    });
}

} // verus!
