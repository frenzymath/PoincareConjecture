import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false

open Set Metric
open scoped BigOperators

namespace Finset

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem centroid_eq_inv_card_smul_sum (s : Finset ι) (hs : s.Nonempty) (p : ι → E) :
    s.centroid ℝ p = (s.card : ℝ)⁻¹ • ∑ i ∈ s, p i := by
  rw [centroid_def, affineCombination_eq_linear_combination _ _ _
    (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
  simp only [centroidWeights_apply, smul_sum]

theorem dist_centroid_le_sdiff_ratio [DecidableEq E] {s t : Finset E}
    (hs : s.Nonempty) (hst : s ⊆ t) {D : ℝ}
    (hdiam : diam (convexHull ℝ (t : Set E)) ≤ D) :
    dist (s.centroid ℝ id) (t.centroid ℝ id) ≤
      ((t \ s).card : ℝ) / (t.card : ℝ) * D := by
  have ht : t.Nonempty := hs.mono hst
  have hsc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  have htc : (t.card : ℝ) ≠ 0 := by exact_mod_cast ht.card_pos.ne'
  have hscent : ∑ v ∈ s, (v - s.centroid ℝ id) = 0 := by
    rw [sum_sub_distrib, sum_const, ← Nat.cast_smul_eq_nsmul ℝ,
      s.centroid_eq_inv_card_smul_sum hs, smul_smul, mul_inv_cancel₀ hsc, one_smul]
    simp only [id_eq, sub_self]
  have hdiff : t.centroid ℝ id - s.centroid ℝ id =
      (t.card : ℝ)⁻¹ • ∑ v ∈ t \ s, (v - s.centroid ℝ id) := by
    have he : ∑ v ∈ t, (v - s.centroid ℝ id) =
        ∑ v ∈ t \ s, (v - s.centroid ℝ id) := by
      rw [← sum_sdiff hst, hscent, add_zero]
    rw [← he, sum_sub_distrib, sum_const, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_sub, smul_smul, inv_mul_cancel₀ htc, one_smul,
      t.centroid_eq_inv_card_smul_sum ht]
    rfl
  have hcs : s.centroid ℝ id ∈ convexHull ℝ (t : Set E) :=
    convexHull_mono hst (s.centroid_mem_convexHull hs)
  have hnorm : ∀ v ∈ t \ s, ‖v - s.centroid ℝ id‖ ≤ D := by
    intro v hv
    rw [← dist_eq_norm]
    exact (dist_le_diam_of_mem (t.finite_toSet.isCompact_convexHull ℝ).isBounded
      (subset_convexHull ℝ _ (mem_sdiff.mp hv).1) hcs).trans hdiam
  calc
    dist (s.centroid ℝ id) (t.centroid ℝ id) =
        ‖t.centroid ℝ id - s.centroid ℝ id‖ := by rw [dist_comm, dist_eq_norm]
    _ = (t.card : ℝ)⁻¹ * ‖∑ v ∈ t \ s, (v - s.centroid ℝ id)‖ := by
      rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
    _ ≤ (t.card : ℝ)⁻¹ * ∑ v ∈ t \ s, ‖v - s.centroid ℝ id‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ ≤ (t.card : ℝ)⁻¹ * ∑ _v ∈ t \ s, D :=
      mul_le_mul_of_nonneg_left (sum_le_sum hnorm) (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = ((t \ s).card : ℝ) / (t.card : ℝ) * D := by
      simp only [sum_const, nsmul_eq_mul, div_eq_mul_inv]
      ring

theorem dist_centroid_le_mesh_factor {s t : Finset E}
    (hs : s.Nonempty) (hst : s ⊆ t) {N : ℕ} (htN : t.card ≤ N + 1)
    {D : ℝ} (hD : 0 ≤ D) (hdiam : diam (convexHull ℝ (t : Set E)) ≤ D) :
    dist (s.centroid ℝ id) (t.centroid ℝ id) ≤
      (N : ℝ) / ((N : ℝ) + 1) * D := by
  classical
  have ht : t.Nonempty := hs.mono hst
  have htc : (0 : ℝ) < t.card := by exact_mod_cast ht.card_pos
  have hNc : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hs1 : (1 : ℝ) ≤ s.card := by exact_mod_cast hs.card_pos
  have hcard : ((t \ s).card : ℝ) = (t.card : ℝ) - (s.card : ℝ) := by
    rw [card_sdiff_of_subset hst, Nat.cast_sub (card_le_card hst)]
  have htN' : (t.card : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast htN
  have hratio : ((t \ s).card : ℝ) / (t.card : ℝ) ≤ (N : ℝ) / ((N : ℝ) + 1) := by
    rw [div_le_div_iff₀ htc hNc, hcard]
    nlinarith
  exact (dist_centroid_le_sdiff_ratio hs hst hdiam).trans (mul_le_mul_of_nonneg_right hratio hD)

end Finset
