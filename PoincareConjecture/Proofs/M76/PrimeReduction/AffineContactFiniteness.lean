import PoincareConjecture.Proofs.M76.Dehn.Mathlib.AffineIntersectionRanks










set_option autoImplicit false

open Set Module

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem finrank_affineSpan_finset_le {s : Finset E} (hs : s.Nonempty)
    {d : ℕ} (hc : s.card ≤ d + 1) :
    finrank ℝ (affineSpan ℝ (s : Set E)).direction ≤ d := by
  let : Nonempty s := hs.to_subtype
  have h := finrank_vectorSpan_range_add_one_le ℝ (fun x : s => (x : E))
  have he : range (fun x : s => (x : E)) = (s : Set E) := by ext x; simp
  rw [he, Fintype.card_coe] at h
  rw [direction_affineSpan]
  omega

variable [FiniteDimensional ℝ E]




theorem subsingleton_convexHulls_inter_of_span_top_of_rank_le
    {s t : Set E} (hspan : affineSpan ℝ (s ∪ t) = ⊤)
    (hrank : finrank ℝ (affineSpan ℝ s).direction +
      finrank ℝ (affineSpan ℝ t).direction ≤ finrank ℝ E) :
    (convexHull ℝ s ∩ convexHull ℝ t).Subsingleton := by
  intro x hx y hy
  let A := affineSpan ℝ s
  let B := affineSpan ℝ t
  have hxA : x ∈ A := convexHull_subset_affineSpan (s := s) hx.1
  have hxB : x ∈ B := convexHull_subset_affineSpan (s := t) hx.2
  have hyA : y ∈ A := convexHull_subset_affineSpan (s := s) hy.1
  have hyB : y ∈ B := convexHull_subset_affineSpan (s := t) hy.2
  have hAB : A ⊔ B = ⊤ := by
    rw [← AffineSubspace.span_union]
    exact hspan
  have he := A.finrank_inf_add_ambient_of_mem_of_sup_top B hxA hxB hAB
  have hz : finrank ℝ (A ⊓ B).direction = 0 := by
    change finrank ℝ A.direction + finrank ℝ B.direction ≤ finrank ℝ E at hrank
    omega
  have hd := (A ⊓ B).vsub_mem_direction ⟨hxA, hxB⟩ ⟨hyA, hyB⟩
  rw [Submodule.finrank_eq_zero.mp hz] at hd
  exact vsub_eq_zero_iff_eq.mp (by simpa using hd)

end Geometry
