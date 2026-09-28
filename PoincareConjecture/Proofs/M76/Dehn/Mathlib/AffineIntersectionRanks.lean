import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Affine.AddTorsor











set_option autoImplicit false

open Set Module

namespace AffineSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem finrank_inf_add_finrank_sup_of_mem
    (A B : AffineSubspace ℝ E) {x : E} (hxA : x ∈ A) (hxB : x ∈ B) :
    finrank ℝ (A ⊓ B).direction + finrank ℝ (A ⊔ B).direction =
      finrank ℝ A.direction + finrank ℝ B.direction := by
  rw [direction_inf_of_mem hxA hxB, direction_sup_eq_sup_direction hxA hxB, add_comm]
  exact Submodule.finrank_sup_add_finrank_inf_eq A.direction B.direction




theorem finrank_inf_add_ambient_of_mem_of_sup_top
    (A B : AffineSubspace ℝ E) {x : E} (hxA : x ∈ A) (hxB : x ∈ B)
  (hAB : A ⊔ B = ⊤) :
    finrank ℝ (A ⊓ B).direction + finrank ℝ E =
      finrank ℝ A.direction + finrank ℝ B.direction := by
  have h := A.finrank_inf_add_finrank_sup_of_mem B hxA hxB
  rw [hAB] at h
  rw [direction_top] at h
  simpa only [finrank_top] using h





theorem disjoint_convexHulls_of_span_top_of_rank_lt
    {s t : Set E} (hspan : affineSpan ℝ (s ∪ t) = ⊤)
    (hrank : finrank ℝ (affineSpan ℝ s).direction +
      finrank ℝ (affineSpan ℝ t).direction < finrank ℝ E) :
    Disjoint (convexHull ℝ s) (convexHull ℝ t) := by
  apply Set.disjoint_left.mpr
  intro x hxs hxt
  have hxA := convexHull_subset_affineSpan (s := s) hxs
  have hxB := convexHull_subset_affineSpan (s := t) hxt
  have hAB : affineSpan ℝ s ⊔ affineSpan ℝ t = ⊤ := by
    rw [← span_union]
    exact hspan
  have h := (affineSpan ℝ s).finrank_inf_add_ambient_of_mem_of_sup_top
    (affineSpan ℝ t) hxA hxB hAB
  omega

end AffineSubspace
