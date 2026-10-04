import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.LocallyPiecewiseAffine
import Mathlib.Geometry.Manifold.StructureGroupoid

/-!+# The piecewise-affine coordinate groupoid

Open partial homeomorphisms with local finite simplicial formulas
in both directions form a restriction-closed structure groupoid.
This gives the coordinate meaning of Hamilton's PL structures.
See Hamilton 1976, pp. 64, 68--69, Hudson 1969, pp. 15--19 and
M76 derivation 80.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Local piecewise-affine maps satisfy the composition and
locality axioms of a pregroupoid. See Hamilton pp. 64, 68--69
and M76 derivation 80. -/
def piecewiseAffinePregroupoid : Pregroupoid E where
  property := LocallyPiecewiseAffineOn
  comp hf hg _ _ _ := hg.comp hf
  id_mem := locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ E) isOpen_univ
  locality _ hf := LocallyPiecewiseAffineOn.locality fun x hx => by
    obtain ⟨V, _, hxV, hV⟩ := hf x hx
    exact ⟨V, hxV, hV⟩
  congr _ hgf hf := hf.congr (fun x hx => (hgf x hx).symm)

/-- PL coordinate changes have local finite simplicial formulas
for both the forward and inverse maps. See Hamilton pp. 64,
68--69, Hudson pp. 15--19 and M76 derivation 80. -/
def piecewiseAffineGroupoid : StructureGroupoid E :=
  (piecewiseAffinePregroupoid E).groupoid

/-- Membership exposes both directions of the PL coordinate
condition. See Hamilton p. 64 and M76 derivation 80. -/
theorem mem_piecewiseAffineGroupoid_iff (e : OpenPartialHomeomorph E E) :
    e ∈ piecewiseAffineGroupoid E ↔
      LocallyPiecewiseAffineOn e e.source ∧ LocallyPiecewiseAffineOn e.symm e.target :=
  Iff.rfl

/-- Restricting a PL coordinate change to an open source keeps
it PL. See Hamilton pp. 68--69 and M76 derivation 80. -/
instance piecewiseAffineGroupoid_closedUnderRestriction :
    ClosedUnderRestriction (piecewiseAffineGroupoid E) where
  closedUnderRestriction := by
    intro e he s _
    change LocallyPiecewiseAffineOn e e.source ∧
      LocallyPiecewiseAffineOn e.symm e.target at he
    exact ⟨he.1.mono (e.restr s).open_source (fun _ hx => hx.1),
      he.2.mono (e.restr s).open_target (fun _ hx => hx.1)⟩

end Geometry
