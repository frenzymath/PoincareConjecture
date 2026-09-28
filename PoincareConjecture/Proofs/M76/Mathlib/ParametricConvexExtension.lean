import PoincareConjecture.Proofs.M76.Mathlib.ContractibleConvexExtension
import PoincareConjecture.Proofs.M76.Mathlib.ContractibleMappingSpace









set_option autoImplicit false

open Set

namespace ContinuousMap

variable {E B Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [TopologicalSpace B] [LocallyCompactSpace B] [TopologicalSpace Y] [ContractibleSpace Y]




theorem exists_convexBody_parametric_extension {C : Set E}
    (hC : IsClosed C) (hc : Convex ℝ C) (hi : (interior C).Nonempty)
    (hb : Bornology.IsBounded C) (f : C(frontier C × B, Y)) :
    ∃ g : C(C × B, Y), ∀ x : frontier C, ∀ b : B,
      g (⟨x, hC.frontier_subset x.property⟩, b) = f (x, b) := by
  let : ContractibleSpace C(B, Y) := contractibleSpace_of_target B Y
  obtain ⟨g, hg⟩ := exists_convexBody_extension_of_contractible hC hc hi hb f.curry
  refine ⟨g.uncurry, ?_⟩
  intro x b
  exact congrArg (fun k : C(B, Y) => k b) (hg x)

end ContinuousMap
