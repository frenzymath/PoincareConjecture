import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# Rank consequences only at actual affine intersections

A real common point identifies the direction of an affine
intersection and removes the extra joining direction in the
affine union. Rank-nullity then gives the crossing dimension.
See Hudson1969, general position on p.90 and Lemma4.5;
Dehn029, section4, retains this nonemptiness requirement.
-/

set_option autoImplicit false

open Set Module

namespace AffineSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- At a common point the ranks of the actual intersection
and affine join add to the two direction ranks. This statement
does not assign a dimension to an empty intersection.
See Dehn029, section4. -/
theorem finrank_inf_add_finrank_sup_of_mem
    (A B : AffineSubspace ℝ E) {x : E} (hxA : x ∈ A) (hxB : x ∈ B) :
    finrank ℝ (A ⊓ B).direction + finrank ℝ (A ⊔ B).direction =
      finrank ℝ A.direction + finrank ℝ B.direction := by
  rw [direction_inf_of_mem hxA hxB, direction_sup_eq_sup_direction hxA hxB, add_comm]
  exact Submodule.finrank_sup_add_finrank_inf_eq A.direction B.direction

/-- Full affine span at an actual intersection gives the exact
ambient rank equation used for PL crossings. See Dehn029,
section4. -/
  theorem finrank_inf_add_ambient_of_mem_of_sup_top
    (A B : AffineSubspace ℝ E) {x : E} (hxA : x ∈ A) (hxB : x ∈ B)
  (hAB : A ⊔ B = ⊤) :
    finrank ℝ (A ⊓ B).direction + finrank ℝ E =
      finrank ℝ A.direction + finrank ℝ B.direction := by
  have h := A.finrank_inf_add_finrank_sup_of_mem B hxA hxB
  rw [hAB] at h
  rw [direction_top] at h
  simpa only [finrank_top] using h

/-- If the directions are too small to meet with full affine
span, the whole convex hulls are disjoint. This conclusion is
derived by assuming a real common point, not by subtracting
natural-number dimensions. See Dehn029, section4. -/
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
