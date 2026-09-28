import PoincareConjecture.Proofs.M34.Lemma12_2_InitialMetric.ProfileBounds
import PoincareConjecture.Definitions.Ch12.StandardCap












set_option autoImplicit false

open scoped ContDiff Topology

namespace PoincareConjecture.M34



noncomputable def capAngularCoefficient (a r : ℝ) : ℝ :=
  if r = 0 then 1 else (capProfile a r / r) ^ 2



noncomputable def capRadialCoefficient (a r : ℝ) : ℝ :=
  if r = 0 then 1 / 12 else (1 - capAngularCoefficient a r) / r ^ 2



theorem capAngularCoefficient_pos {a r : ℝ} (ha : 0 ≤ a)
    (hapi : a ≤ Real.pi / 2) (hr : 0 ≤ r) : 0 < capAngularCoefficient a r := by
  by_cases h : r = 0
  · simp only [capAngularCoefficient, h, if_true]
    norm_num
  · rw [capAngularCoefficient, if_neg h]
    exact sq_pos_of_pos (div_pos (capProfile_pos ha hapi (lt_of_le_of_ne hr (Ne.symm h)))
      (lt_of_le_of_ne hr (Ne.symm h)))



theorem capAngularCoefficient_le_one {a r : ℝ} (ha : 0 ≤ a)
    (hapi : a ≤ Real.pi / 2) (hr : 0 ≤ r) : capAngularCoefficient a r ≤ 1 := by
  by_cases h : r = 0
  · simp only [capAngularCoefficient, h, if_true, le_refl]
  · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm h)
    have hpos : 0 ≤ capProfile a r / r := (div_pos (capProfile_pos ha hapi hrp) hrp).le
    have hle : capProfile a r / r ≤ 1 :=
      (div_le_one hrp).mpr (capProfile_le_radius a hr)
    rw [capAngularCoefficient, if_neg h]
    nlinarith


theorem capRadialCoefficient_nonneg {a r : ℝ} (ha : 0 ≤ a)
    (hapi : a ≤ Real.pi / 2) (hr : 0 ≤ r) : 0 ≤ capRadialCoefficient a r := by
  by_cases h : r = 0
  · simp only [capRadialCoefficient, h, if_true]
    norm_num
  · rw [capRadialCoefficient, if_neg h]
    exact div_nonneg (sub_nonneg.mpr (capAngularCoefficient_le_one ha hapi hr))
      (sq_nonneg r)



noncomputable def capMetricInner (a : ℝ) (x : StandardCapSpace) :
    StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ :=
  let B : StandardCapSpace →L[ℝ] StandardCapSpace →L[ℝ] ℝ := innerSL ℝ
  capAngularCoefficient a ‖x‖ • B +
    capRadialCoefficient a ‖x‖ • (B x).smulRight (B x)



theorem capMetricInner_apply (a : ℝ) (x u v : StandardCapSpace) :
    capMetricInner a x u v = capAngularCoefficient a ‖x‖ * inner ℝ u v +
      capRadialCoefficient a ‖x‖ * (inner ℝ x u * inner ℝ x v) := rfl



theorem capMetricInner_zero (a : ℝ) (u v : StandardCapSpace) :
    capMetricInner a 0 u v = inner ℝ u v := by
  simp only [capMetricInner_apply, norm_zero, capAngularCoefficient, if_true,
    inner_zero_left, mul_zero, one_mul, add_zero]


theorem capMetricInner_symm (a : ℝ) (x u v : StandardCapSpace) :
    capMetricInner a x u v = capMetricInner a x v u := by
  rw [capMetricInner_apply, capMetricInner_apply, real_inner_comm u v,
    mul_comm (inner ℝ x u) (inner ℝ x v)]



theorem capMetricInner_pos {a : ℝ} (ha : 0 ≤ a) (hapi : a ≤ Real.pi / 2)
    (x v : StandardCapSpace) (hv : v ≠ 0) : 0 < capMetricInner a x v v := by
  rw [capMetricInner_apply]
  exact add_pos_of_pos_of_nonneg
    (mul_pos (capAngularCoefficient_pos ha hapi (norm_nonneg x))
      (real_inner_self_pos.mpr hv))
    (mul_nonneg (capRadialCoefficient_nonneg ha hapi (norm_nonneg x))
      (mul_self_nonneg _))



theorem capMetricInner_radial (a : ℝ) (x : StandardCapSpace) :
    capMetricInner a x x x = ‖x‖ ^ 2 := by
  by_cases hx : x = 0
  · simp only [hx, capMetricInner_zero, inner_zero_left, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    rw [capMetricInner_apply, real_inner_self_eq_norm_sq, capRadialCoefficient, if_neg hn]
    field_simp
    ring



theorem capMetricInner_linearIsometry (a : ℝ)
    (A : StandardCapSpace →ₗᵢ[ℝ] StandardCapSpace) (x u v : StandardCapSpace) :
    capMetricInner a (A x) (A u) (A v) = capMetricInner a x u v := by
  simp only [capMetricInner_apply, A.norm_map, A.inner_map_map]

end PoincareConjecture.M34
