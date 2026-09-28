import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicFaceSaturation
import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineHeightSigns









set_option autoImplicit false

open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem Convex.mem_both_height_closures_of_intrinsicInterior
    {C : Set E} (hC : Convex ℝ C) (L : E →ᵃ[ℝ] ℝ)
    {p : E} (hp : p ∈ intrinsicInterior ℝ C) (hpzero : L p = 0)
    (hne : ∃ v ∈ C, L v ≠ 0) :
    p ∈ closure (C ∩ {x | L x < 0}) ∧
      p ∈ closure (C ∩ {x | 0 < L x}) := by
  obtain ⟨v, hv, hvzero⟩ := hne
  have hpC : p ∈ C := intrinsicInterior_subset hp
  have hdir : p - v ∈ (affineSpan ℝ C).direction :=
    (affineSpan ℝ C).vsub_mem_direction (subset_affineSpan ℝ C hpC)
      (subset_affineSpan ℝ C hv)
  obtain ⟨r, hr, hrC⟩ := Set.exists_pos_smul_add_mem_of_intrinsicInterior hp hdir
  have hrL : L (r • (p - v) + p) = -(r * L v) := by
    change L (r • (p -ᵥ v) +ᵥ p) = -(r * L v)
    rw [L.map_vadd, map_smul, L.linearMap_vsub]
    simp only [vsub_eq_sub, vadd_eq_add, smul_eq_mul, hpzero, zero_sub, mul_neg, add_zero]
  have hsigns : (∃ x ∈ C, L x < 0) ∧ ∃ y ∈ C, 0 < L y := by
    rcases lt_or_gt_of_ne hvzero with hneg | hpos
    · refine ⟨⟨v, hv, hneg⟩, ⟨r • (p - v) + p, hrC, ?_⟩⟩
      rw [hrL]
      exact neg_pos.mpr (mul_neg_of_pos_of_neg hr hneg)
    · refine ⟨⟨r • (p - v) + p, hrC, ?_⟩, ⟨v, hv, hpos⟩⟩
      rw [hrL]
      exact neg_neg_of_pos (mul_pos hr hpos)
  obtain ⟨⟨x, hx, hxL⟩, ⟨y, hy, hyL⟩⟩ := hsigns
  have hneg := hC.mem_closure_lower_affine_height L hpC hx (by simpa only [hpzero] using hxL)
  have hpos := hC.mem_closure_upper_affine_height L hpC hy (by simpa only [hpzero] using hyL)
  simpa only [hpzero] using And.intro hneg hpos



theorem Set.mem_both_height_closures_of_intrinsicInterior_convexHull
    (s : Finset E) (L : E →ᵃ[ℝ] ℝ) {p : E}
    (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hpzero : L p = 0) (hne : ∃ v ∈ s, L v ≠ 0) :
    p ∈ closure (convexHull ℝ (s : Set E) ∩ {x | L x < 0}) ∧
      p ∈ closure (convexHull ℝ (s : Set E) ∩ {x | 0 < L x}) := by
  obtain ⟨v, hv, hvL⟩ := hne
  exact (convex_convexHull ℝ (s : Set E)).mem_both_height_closures_of_intrinsicInterior
    L hp hpzero ⟨v, subset_convexHull ℝ _ hv, hvL⟩
