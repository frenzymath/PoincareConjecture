import PoincareConjecture.Proofs.M38.ParameterizedBallShrinking
import PoincareConjecture.Proofs.M38.LinearSphereDiffeomorph
import PoincareConjecture.Proofs.M38.SphereMonodromy










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology Filter
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

variable (L : StandardCapSpace ≃L[ℝ] StandardCapSpace)


noncomputable def directionalRadialScale : ℝ :=
  1 / (2 * (‖(L.symm : StandardCapSpace →L[ℝ] StandardCapSpace)‖ + 1))


theorem directionalRadialScale_pos : 0 < directionalRadialScale L := by
  unfold directionalRadialScale
  positivity


noncomputable def directionalRadialCoefficient (w : UnitTwoSphere) : ℝ :=
  directionalRadialScale L * ‖L.symm w.val‖


theorem directionalRadialCoefficient_bounds (w : UnitTwoSphere) :
    0 < directionalRadialCoefficient L w ∧ directionalRadialCoefficient L w < 1 := by
  have hscale := directionalRadialScale_pos L
  have hnorm := (L.symm : StandardCapSpace →L[ℝ] StandardCapSpace).le_opNorm w.val
  simp only [show ‖w.val‖ = 1 by simp, mul_one] at hnorm
  have hhalf : directionalRadialScale L *
      (‖(L.symm : StandardCapSpace →L[ℝ] StandardCapSpace)‖ + 1) = 1 / 2 := by
    unfold directionalRadialScale
    field_simp
  constructor
  · exact mul_pos hscale (norm_pos_iff.mpr (linearSphereVector_ne_zero L.symm w))
  · unfold directionalRadialCoefficient
    calc
      directionalRadialScale L * ‖L.symm w.val‖ ≤ directionalRadialScale L *
          ‖(L.symm : StandardCapSpace →L[ℝ] StandardCapSpace)‖ :=
        mul_le_mul_of_nonneg_left hnorm hscale.le
      _ < 1 := by nlinarith


theorem capUnitDirectionVector_contDiffAt {x : StandardCapSpace} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : StandardCapSpace => (capUnitDirection y).val) x := by
  have h : ContDiffAt ℝ ∞ (fun y : StandardCapSpace => ‖y‖⁻¹ • y) x :=
    ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id
  apply h.congr_of_eventuallyEq
  have hnear : ∀ᶠ y : StandardCapSpace in 𝓝 x, y ≠ 0 :=
    isOpen_compl_singleton.mem_nhds hx
  exact hnear.mono (fun y hy => capUnitDirection_coe hy)


theorem directionalRadialCoefficient_contDiffAt {x : StandardCapSpace} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => directionalRadialCoefficient L (capUnitDirection y)) x := by
  have hlin : ContDiffAt ℝ ∞
      (fun y : StandardCapSpace => L.symm (capUnitDirection y).val) x :=
    L.symm.contDiff.contDiffAt.comp x (capUnitDirectionVector_contDiffAt hx)
  exact contDiffAt_const.mul ((contDiffAt_norm ℝ
    (linearSphereVector_ne_zero L.symm (capUnitDirection x))).comp x hlin)


noncomputable def directionalRadialMap (ρ : ℝ) (x : StandardCapSpace) : StandardCapSpace :=
  (ρ * ballShrinkProfile (directionalRadialCoefficient L (capUnitDirection x)) (‖x‖ / ρ)) •
    (capUnitDirection x).val


noncomputable def directionalRadialInverse (ρ : ℝ) (x : StandardCapSpace) : StandardCapSpace :=
  (ρ * parameterizedBallShrinkInverse
    (directionalRadialCoefficient L (capUnitDirection x)) (‖x‖ / ρ)) •
      (capUnitDirection x).val

variable {ρ : ℝ} (hρ : 0 < ρ)

include hρ


theorem directionalRadialMap_radius_pos {x : StandardCapSpace} (hx : x ≠ 0) :
    0 < ρ * ballShrinkProfile (directionalRadialCoefficient L (capUnitDirection x))
      (‖x‖ / ρ) := by
  obtain ⟨hc, hc1⟩ := directionalRadialCoefficient_bounds L (capUnitDirection x)
  apply mul_pos hρ
  simpa only [ballShrinkProfile_zero] using
    (ballShrinkProfile_strictMono hc hc1) (div_pos (norm_pos_iff.mpr hx) hρ)


theorem directionalRadialInverse_radius_pos {x : StandardCapSpace} (hx : x ≠ 0) :
    0 < ρ * parameterizedBallShrinkInverse
      (directionalRadialCoefficient L (capUnitDirection x)) (‖x‖ / ρ) := by
  obtain ⟨hc, hc1⟩ := directionalRadialCoefficient_bounds L (capUnitDirection x)
  exact mul_pos hρ (parameterizedBallShrinkInverse_pos hc hc1
    (div_pos (norm_pos_iff.mpr hx) hρ))


theorem directionalRadialMap_direction {x : StandardCapSpace} (hx : x ≠ 0) :
    capUnitDirection (directionalRadialMap L ρ x) = capUnitDirection x :=
  capUnitDirection_smul _ (directionalRadialMap_radius_pos L hρ hx)


theorem directionalRadialInverse_direction {x : StandardCapSpace} (hx : x ≠ 0) :
    capUnitDirection (directionalRadialInverse L ρ x) = capUnitDirection x :=
  capUnitDirection_smul _ (directionalRadialInverse_radius_pos L hρ hx)


theorem directionalRadialMap_norm {x : StandardCapSpace} (hx : x ≠ 0) :
    ‖directionalRadialMap L ρ x‖ =
      ρ * ballShrinkProfile (directionalRadialCoefficient L (capUnitDirection x))
        (‖x‖ / ρ) := by
  simp only [directionalRadialMap, norm_smul, Real.norm_eq_abs,
    abs_of_pos (directionalRadialMap_radius_pos L hρ hx),
    show ‖(capUnitDirection x).val‖ = 1 by simp, mul_one]


theorem directionalRadialInverse_norm {x : StandardCapSpace} (hx : x ≠ 0) :
    ‖directionalRadialInverse L ρ x‖ =
      ρ * parameterizedBallShrinkInverse
        (directionalRadialCoefficient L (capUnitDirection x)) (‖x‖ / ρ) := by
  simp only [directionalRadialInverse, norm_smul, Real.norm_eq_abs,
    abs_of_pos (directionalRadialInverse_radius_pos L hρ hx),
    show ‖(capUnitDirection x).val‖ = 1 by simp, mul_one]


theorem directionalRadialMap_ne_zero {x : StandardCapSpace} (hx : x ≠ 0) :
    directionalRadialMap L ρ x ≠ 0 := by
  apply norm_pos_iff.mp
  rw [directionalRadialMap_norm L hρ hx]
  exact directionalRadialMap_radius_pos L hρ hx


theorem directionalRadialInverse_ne_zero {x : StandardCapSpace} (hx : x ≠ 0) :
    directionalRadialInverse L ρ x ≠ 0 := by
  apply norm_pos_iff.mp
  rw [directionalRadialInverse_norm L hρ hx]
  exact directionalRadialInverse_radius_pos L hρ hx


theorem directionalRadial_left_inverse {x : StandardCapSpace} (hx : x ≠ 0) :
    directionalRadialInverse L ρ (directionalRadialMap L ρ x) = x := by
  obtain ⟨hc, hc1⟩ := directionalRadialCoefficient_bounds L (capUnitDirection x)
  rw [directionalRadialInverse, directionalRadialMap_direction L hρ hx,
    directionalRadialMap_norm L hρ hx, mul_div_cancel_left₀ _ hρ.ne',
    parameterizedBallShrinkInverse_left hc hc1, mul_div_cancel₀ _ hρ.ne',
    capUnitDirection_radial]


theorem directionalRadial_right_inverse {x : StandardCapSpace} (hx : x ≠ 0) :
    directionalRadialMap L ρ (directionalRadialInverse L ρ x) = x := by
  obtain ⟨hc, hc1⟩ := directionalRadialCoefficient_bounds L (capUnitDirection x)
  rw [directionalRadialMap, directionalRadialInverse_direction L hρ hx,
    directionalRadialInverse_norm L hρ hx, mul_div_cancel_left₀ _ hρ.ne',
    parameterizedBallShrinkInverse_right hc hc1, mul_div_cancel₀ _ hρ.ne',
    capUnitDirection_radial]

omit hρ in

theorem directionalRadialMap_contDiffAt {x : StandardCapSpace} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (directionalRadialMap L ρ) x := by
  exact (contDiffAt_const.mul (ballShrinkProfile_joint_smooth.contDiffAt.comp x
    ((directionalRadialCoefficient_contDiffAt L hx).prodMk
      ((contDiffAt_norm ℝ hx).div_const ρ)))).smul (capUnitDirectionVector_contDiffAt hx)

omit hρ in

theorem directionalRadialInverse_contDiffAt {x : StandardCapSpace} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (directionalRadialInverse L ρ) x := by
  obtain ⟨hc, hc1⟩ := directionalRadialCoefficient_bounds L (capUnitDirection x)
  exact (contDiffAt_const.mul
    ((parameterizedBallShrinkInverse_contDiffAt hc hc1 (‖x‖ / ρ)).comp x
      ((directionalRadialCoefficient_contDiffAt L hx).prodMk
        ((contDiffAt_norm ℝ hx).div_const ρ)))).smul (capUnitDirectionVector_contDiffAt hx)


noncomputable def directionalRadialDiffeomorph :
    Diffeomorph (𝓡 3) (𝓡 3) monodromyPunctureOpen monodromyPunctureOpen ∞ where
  toFun x := ⟨directionalRadialMap L ρ x.val, directionalRadialMap_ne_zero L hρ x.property⟩
  invFun x := ⟨directionalRadialInverse L ρ x.val,
    directionalRadialInverse_ne_zero L hρ x.property⟩
  left_inv x := Subtype.ext (directionalRadial_left_inverse L hρ x.property)
  right_inv x := Subtype.ext (directionalRadial_right_inverse L hρ x.property)
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff monodromyPunctureOpen _).mp
    intro x
    change ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (fun y : monodromyPunctureOpen => directionalRadialMap L ρ y.val) x
    apply (contMDiffAt_subtype_iff (U := monodromyPunctureOpen)
      (f := directionalRadialMap L ρ)).mpr
    exact (directionalRadialMap_contDiffAt L x.property).contMDiffAt
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff monodromyPunctureOpen _).mp
    intro x
    change ContMDiffAt (𝓡 3) (𝓡 3) ∞
      (fun y : monodromyPunctureOpen => directionalRadialInverse L ρ y.val) x
    apply (contMDiffAt_subtype_iff (U := monodromyPunctureOpen)
      (f := directionalRadialInverse L ρ)).mpr
    exact (directionalRadialInverse_contDiffAt L x.property).contMDiffAt


theorem directionalRadialMap_outer {x : StandardCapSpace} (hx : (3 / 2) * ρ ≤ ‖x‖) :
    directionalRadialMap L ρ x = x := by
  rw [directionalRadialMap, ballShrinkProfile_outer _ _ ((le_div_iff₀ hρ).mpr hx),
    mul_div_cancel₀ _ hρ.ne', capUnitDirection_radial]


theorem directionalRadialInverse_outer {x : StandardCapSpace} (hx : (3 / 2) * ρ ≤ ‖x‖) :
    directionalRadialInverse L ρ x = x := by
  obtain ⟨hc, hc1⟩ := directionalRadialCoefficient_bounds L (capUnitDirection x)
  rw [directionalRadialInverse,
    parameterizedBallShrinkInverse_outer hc hc1 ((le_div_iff₀ hρ).mpr hx),
    mul_div_cancel₀ _ hρ.ne', capUnitDirection_radial]


theorem directionalRadialMap_inner {x : StandardCapSpace} (hx : ‖x‖ ≤ (5 / 4) * ρ) :
    directionalRadialMap L ρ x =
      (directionalRadialScale L * ‖L.symm x‖) • (capUnitDirection x).val := by
  rw [directionalRadialMap, ballShrinkProfile_linear _ _ ((div_le_iff₀ hρ).mpr hx)]
  have hnorm : ‖L.symm x‖ = ‖x‖ * ‖L.symm (capUnitDirection x).val‖ := by
    conv_lhs => rw [← capUnitDirection_radial x]
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
  rw [hnorm, directionalRadialCoefficient]
  congr 1
  field_simp


theorem directionalRadialMap_linear_ray (z : UnitTwoSphere) {t : ℝ} (ht : 0 < t)
    (hinner : ‖L (t • z.val)‖ ≤ (5 / 4) * ρ) :
    directionalRadialMap L ρ (L (t • z.val)) =
      (directionalRadialScale L * t) • (linearSphereDiffeomorph L z).val := by
  rw [directionalRadialMap_inner L hρ hinner, L.symm_apply_apply,
    norm_smul, Real.norm_eq_abs, abs_of_pos ht, show ‖z.val‖ = 1 by simp, mul_one]
  have hdir : capUnitDirection (L (t • z.val)) = linearSphereDiffeomorph L z := by
    rw [linearSphereDiffeomorph_ray]
    exact capUnitDirection_smul _
      (mul_pos ht (norm_pos_iff.mpr (linearSphereVector_ne_zero L z)))
  rw [hdir]

end PoincareConjecture.M38
