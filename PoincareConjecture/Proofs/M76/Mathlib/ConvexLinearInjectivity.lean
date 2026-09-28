import PoincareConjecture.Proofs.M76.Mathlib.AffineIndependentLocalMap
import PoincareConjecture.Proofs.M76.Mathlib.FaceStarInjectivity









set_option autoImplicit false

open Set
open scoped Pointwise

namespace LinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [AddCommGroup F] [Module ℝ F]



theorem injOn_affineSpan_of_injOn_convex (Q : E →ₗ[ℝ] F) {C : Set E}
    (hC : Convex ℝ C) (hne : C.Nonempty) (hQ : InjOn Q C) :
    InjOn Q (affineSpan ℝ C) := by
  obtain ⟨p, hp⟩ := Set.Nonempty.intrinsicInterior hC hne
  have hpC := intrinsicInterior_subset hp
  have hsaturated := (Set.injOn_add_direction_iff hp
    (fun q hq => hC.starConvex hq) Q).mpr hQ
  apply hsaturated.mono
  intro x hx
  refine ⟨p, hpC, x - p,
    (affineSpan ℝ C).vsub_mem_direction hx (subset_affineSpan ℝ C hpC), ?_⟩
  abel_nf




theorem affineIndependent_comp_of_injOn_convexHull {ι : Type*} (Q : E →ₗ[ℝ] F)
    {p : ι → E} (hp : AffineIndependent ℝ p)
    (hQ : InjOn Q (convexHull ℝ (Set.range p))) : AffineIndependent ℝ (Q ∘ p) := by
  cases isEmpty_or_nonempty ι with
  | inl h => exact affineIndependent_of_subsingleton ℝ _
  | inr h =>
    have hspan := Q.injOn_affineSpan_of_injOn_convex (convex_convexHull ℝ _)
      (Set.range_nonempty p).convexHull hQ
    rw [affineSpan_convexHull] at hspan
    exact hp.map_of_injOn_affineSpan Q.toAffineMap hspan

end LinearMap
