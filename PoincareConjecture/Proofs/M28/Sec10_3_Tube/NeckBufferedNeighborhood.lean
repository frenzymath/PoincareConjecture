import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.NeckRestriction
import PoincareConjecture.Proofs.M25.AppA_1_Necks.OverlapSlab

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem restrict_compactClosure (N : EpsilonNeck g) {eta : ℝ}
    (h : N.epsilon < eta) (heta : eta < 1 / 2) :
    IsCompact (closure (N.restrict_m28 eta h.le heta).carrier) ∧
      closure (N.restrict_m28 eta h.le heta).carrier ⊆ N.carrier := by
  have hgap : eta⁻¹ < N.epsilon⁻¹ := (inv_lt_inv₀
    (N.epsilon_pos.trans h) N.epsilon_pos).mpr h
  let K := N.coordinate_map '' (univ ×ˢ Icc (-eta⁻¹) eta⁻¹)
  have hK : IsCompact K := N.isCompact_coordinate_slab_intrinsic
    (neg_lt_neg hgap) hgap
  have hsub : (N.restrict_m28 eta h.le heta).carrier ⊆ K := by
    intro x hx
    exact ⟨N.coordinate_inverse x, ⟨mem_univ _, hx.2.1.le, hx.2.2.le⟩,
      N.coordinate_map_coordinate_inverse hx.1⟩
  have hclosure := closure_minimal hsub hK.isClosed
  exact ⟨hK.of_isClosed_subset isClosed_closure hclosure,
    hclosure.trans (N.coordinate_slab_subset_carrier_m28 (neg_lt_neg hgap) hgap)⟩

theorem buffered_intrinsicEDist_lt [T3Space M]
    (N : EpsilonNeck g) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hsmall : epsilon ≤ 1 / 10000) (heq : N.epsilon = 3 * epsilon / 2)
    {y : M} (hy : y ∈ N.carrier)
    (hheight : |(N.coordinate_inverse y).2| ≤ 3 * epsilon⁻¹ / 5) :
    intrinsicEDist g (N.region (-(8 * epsilon / 5)⁻¹) (8 * epsilon / 5)⁻¹)
      N.center y < ENNReal.ofReal ((61 / 100 : ℝ) * N.scale * epsilon⁻¹) := by
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  have heta : N.epsilon ≤ 8 * epsilon / 5 := by rw [heq]; linarith
  have hetahalf : 8 * epsilon / 5 < 1 / 2 := by linarith
  let R := N.restrict_m28 (8 * epsilon / 5) heta hetahalf
  have hinv : 0 < epsilon⁻¹ := inv_pos.mpr hepsilon
  have hwidth : (8 * epsilon / 5)⁻¹ = 5 * epsilon⁻¹ / 8 := by
    field_simp
  have hyR : y ∈ R.carrier := by
    refine ⟨hy, ?_⟩
    rw [hwidth]
    exact abs_lt.mp (hheight.trans_lt (by linarith))
  have hc : R.center ∈ R.carrier := R.central_sphere_subset R.center_on_central_sphere
  have hzero : (R.coordinate_inverse R.center).2 = 0 :=
    ((R.mem_central_sphere_iff R.center).mp R.center_on_central_sphere).2
  have hd := R.intrinsicEDist_le_axial_add hc hyR
  rw [hzero, sub_zero] at hd
  have hsqrt : Real.sqrt (1 + 8 * epsilon / 5) ≤ 1001 / 1000 :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num, by linarith⟩
  have hsphere : Real.sqrt 2 * (Real.pi + 1) ≤ 10 := by
    have hs : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
    have hp : Real.pi + 1 ≤ 5 := by linarith [Real.pi_lt_four]
    exact (mul_le_mul hs hp (by positivity) (by norm_num)).trans (by norm_num)
  have hwide : (10000 : ℝ) ≤ epsilon⁻¹ := by
    simpa only [one_div, inv_inv] using one_div_le_one_div_of_le hepsilon hsmall
  have hsum : |(N.coordinate_inverse y).2| + Real.sqrt 2 * (Real.pi + 1) ≤
      (601 / 1000 : ℝ) * epsilon⁻¹ := by linarith
  have hupper : N.scale * Real.sqrt (1 + 8 * epsilon / 5) *
      (|(N.coordinate_inverse y).2| + Real.sqrt 2 * (Real.pi + 1)) ≤
        N.scale * (1001 / 1000) * ((601 / 1000) * epsilon⁻¹) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left hsqrt N.scale_pos.le) hsum
      (by positivity) (mul_nonneg N.scale_pos.le (by norm_num))
  have hstrict : N.scale * (1001 / 1000) * ((601 / 1000) * epsilon⁻¹) <
      (61 / 100 : ℝ) * N.scale * epsilon⁻¹ := by
    nlinarith only [mul_pos N.scale_pos hinv]
  exact hd.trans_lt ((ENNReal.ofReal_lt_ofReal_iff
    (mul_pos (mul_pos (by norm_num) N.scale_pos) hinv)).mpr
      (hupper.trans_lt hstrict))

end PoincareConjecture.EpsilonNeck
