import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffine
import Mathlib.Geometry.Manifold.StructureGroupoid

set_option autoImplicit false

open Set

namespace Geometry

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

def piecewiseAffinePregroupoid : Pregroupoid E where
  property := LocallyPiecewiseAffineOn
  comp hf hg _ _ _ := hg.comp hf
  id_mem := locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ E) isOpen_univ
  locality _ hf := LocallyPiecewiseAffineOn.locality fun x hx => by
    obtain ⟨V, _, hxV, hV⟩ := hf x hx
    exact ⟨V, hxV, hV⟩
  congr _ hgf hf := hf.congr (fun x hx => (hgf x hx).symm)

def piecewiseAffineGroupoid : StructureGroupoid E :=
  (piecewiseAffinePregroupoid E).groupoid

theorem mem_piecewiseAffineGroupoid_iff (e : OpenPartialHomeomorph E E) :
    e ∈ piecewiseAffineGroupoid E ↔
      LocallyPiecewiseAffineOn e e.source ∧ LocallyPiecewiseAffineOn e.symm e.target :=
  Iff.rfl

instance piecewiseAffineGroupoid_closedUnderRestriction :
    ClosedUnderRestriction (piecewiseAffineGroupoid E) where
  closedUnderRestriction := by
    intro e he s _
    change LocallyPiecewiseAffineOn e e.source ∧
      LocallyPiecewiseAffineOn e.symm e.target at he
    exact ⟨he.1.mono (e.restr s).open_source (fun _ hx => hx.1),
      he.2.mono (e.restr s).open_target (fun _ hx => hx.1)⟩

end Geometry
