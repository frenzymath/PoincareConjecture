import PoincareConjecture.Proofs.M38.NormalScale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M38

variable {a : ℝ} (ha : 0 < a) (ha1 : a < 1)

noncomputable def normalRadiusOrderIso : ℝ ≃o ℝ :=
  (OrderIso.subRight (1 : ℝ)).trans
    ((normalScaleOrderIso a ha ha1).trans (OrderIso.addLeft 1))

theorem normalRadiusOrderIso_apply (t : ℝ) :
    normalRadiusOrderIso ha ha1 t = 1 + normalScaleProfile a (t - 1) := rfl

theorem normalRadiusOrderIso_symm_apply (t : ℝ) :
    (normalRadiusOrderIso ha ha1).symm t =
      1 + (normalScaleOrderIso a ha ha1).symm (t - 1) := by
  apply (normalRadiusOrderIso ha ha1).injective
  rw [OrderIso.apply_symm_apply]
  change t = 1 + normalScaleOrderIso a ha ha1
    (1 + (normalScaleOrderIso a ha ha1).symm (t - 1) - 1)
  rw [add_sub_cancel_left, OrderIso.apply_symm_apply]
  ring

theorem normalRadiusOrderIso_outer {t : ℝ} (ht : 1 / 4 ≤ |t - 1|) :
    normalRadiusOrderIso ha ha1 t = t := by
  rw [normalRadiusOrderIso_apply, normalScaleProfile_outer a ht]
  ring

theorem normalRadiusOrderIso_symm_outer {t : ℝ} (ht : 1 / 4 ≤ |t - 1|) :
    (normalRadiusOrderIso ha ha1).symm t = t := by
  apply (normalRadiusOrderIso ha ha1).injective
  rw [OrderIso.apply_symm_apply, normalRadiusOrderIso_outer ha ha1 ht]

@[simp] theorem normalRadiusOrderIso_zero : normalRadiusOrderIso ha ha1 0 = 0 :=
  normalRadiusOrderIso_outer ha ha1 (by norm_num)

@[simp] theorem normalRadiusOrderIso_one : normalRadiusOrderIso ha ha1 1 = 1 := by
  rw [normalRadiusOrderIso_apply, sub_self,
    normalScaleProfile_inner a (by norm_num : |(0 : ℝ)| ≤ 1 / 8)]
  ring

@[simp] theorem normalRadiusOrderIso_two : normalRadiusOrderIso ha ha1 2 = 2 :=
  normalRadiusOrderIso_outer ha ha1 (by norm_num)

@[simp] theorem normalRadiusOrderIso_symm_zero : (normalRadiusOrderIso ha ha1).symm 0 = 0 :=
  normalRadiusOrderIso_symm_outer ha ha1 (by norm_num)

@[simp] theorem normalRadiusOrderIso_symm_one : (normalRadiusOrderIso ha ha1).symm 1 = 1 := by
  apply (normalRadiusOrderIso ha ha1).injective
  simp

@[simp] theorem normalRadiusOrderIso_symm_two : (normalRadiusOrderIso ha ha1).symm 2 = 2 :=
  normalRadiusOrderIso_symm_outer ha ha1 (by norm_num)

theorem normalRadiusOrderIso_smooth : ContDiff ℝ ∞ (normalRadiusOrderIso ha ha1) := by
  change ContDiff ℝ ∞ (fun t : ℝ => 1 + normalScaleProfile a (t - 1))
  exact contDiff_const.add ((normalScaleProfile_smooth a).comp
    (contDiff_id.sub contDiff_const))

theorem normalRadiusOrderIso_symm_smooth :
    ContDiff ℝ ∞ (normalRadiusOrderIso ha ha1).symm := by
  rw [show ((normalRadiusOrderIso ha ha1).symm : ℝ → ℝ) = _ from
    funext (normalRadiusOrderIso_symm_apply ha ha1)]
  exact contDiff_const.add ((normalScaleOrderIso_symm_smooth ha ha1).comp
    (contDiff_id.sub contDiff_const))

noncomputable def normalRadialExpansion :
    Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞ where
  toFun := capRadialMap (normalRadiusOrderIso ha ha1).symm
  invFun := capRadialMap (normalRadiusOrderIso ha ha1)
  left_inv := capRadialMap_left_inverse _ (normalRadiusOrderIso_symm_zero ha ha1)
  right_inv := capRadialMap_left_inverse _ (normalRadiusOrderIso_zero ha ha1)
  contMDiff_toFun := (capRadialMap_smooth _ (normalRadiusOrderIso_symm_smooth ha ha1)
    (1 / 2) 1 (by norm_num) (fun t ht => by
      rw [normalRadiusOrderIso_symm_outer ha ha1 (by
        rw [abs_of_nonpos (by linarith : t - 1 ≤ 0)]
        linarith), one_mul])).contMDiff
  contMDiff_invFun := (capRadialMap_smooth _ (normalRadiusOrderIso_smooth ha ha1)
    (1 / 2) 1 (by norm_num) (fun t ht => by
      rw [normalRadiusOrderIso_outer ha ha1 (by
        rw [abs_of_nonpos (by linarith : t - 1 ≤ 0)]
        linarith), one_mul])).contMDiff

theorem normalRadialExpansion_norm (x : StandardCapSpace) :
    ‖normalRadialExpansion ha ha1 x‖ = (normalRadiusOrderIso ha ha1).symm ‖x‖ := by
  apply capRadialMap_norm _ (normalRadiusOrderIso_symm_zero ha ha1)
  intro t ht
  simpa using (normalRadiusOrderIso ha ha1).symm.monotone ht

theorem normalRadialExpansion_mapsTo :
    MapsTo (normalRadialExpansion ha ha1) (Metric.ball 0 2) (Metric.ball 0 2) := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right, normalRadialExpansion_norm]
  have h := (normalRadiusOrderIso ha ha1).symm.strictMono
    (show ‖x‖ < 2 by simpa only [Metric.mem_ball, dist_zero_right] using hx)
  simpa using h

theorem normalRadialExpansion_closedBall :
    normalRadialExpansion ha ha1 '' Metric.closedBall 0 1 = Metric.closedBall 0 1 := by
  ext y
  obtain ⟨x, rfl⟩ := (normalRadialExpansion ha ha1).surjective y
  change normalRadialExpansion ha ha1 x ∈
      normalRadialExpansion ha ha1 '' Metric.closedBall 0 1 ↔
      normalRadialExpansion ha ha1 x ∈ Metric.closedBall 0 1
  have himage : normalRadialExpansion ha ha1 x ∈
      normalRadialExpansion ha ha1 '' Metric.closedBall 0 1 ↔
      x ∈ Metric.closedBall 0 1 := by
    constructor
    · rintro ⟨z, hz, heq⟩
      exact (normalRadialExpansion ha ha1).injective heq ▸ hz
    · exact mem_image_of_mem _
  rw [himage]
  simp only [Metric.mem_closedBall, dist_zero_right, normalRadialExpansion_norm]
  rw [← normalRadiusOrderIso_symm_one ha ha1,
    (normalRadiusOrderIso ha ha1).symm.le_iff_le]
  rw [normalRadiusOrderIso_symm_one]

theorem normalRadialExpansion_annulus (z : UnitTwoSphere) {s : ℝ}
    (hs : |s| ≤ a / 8) :
    normalRadialExpansion ha ha1 ((1 + s) • z.val) = (1 + s / a) • z.val := by
  have hpos : 0 < 1 + s := by have h := (abs_le.mp hs).1; linarith
  change capRadialMap (normalRadiusOrderIso ha ha1).symm ((1 + s) • z.val) = _
  rw [capRadialMap, norm_smul, Real.norm_eq_abs, abs_of_pos hpos,
    show ‖z.val‖ = 1 by simp, mul_one, smul_smul, div_mul_cancel₀ _ hpos.ne',
    normalRadiusOrderIso_symm_apply, add_sub_cancel_left,
    normalScaleOrderIso_symm_inner ha ha1 hs]

end PoincareConjecture.M38
