import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityPolarMeasure
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.L2Coefficients










set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace PoincareConjecture.M65Interior

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




def polarPullbackL2 (x : LoopPlane) {ε : ℝ} (R : ℝ) (hε : 0 < ε) :
    Lp E 2 (volume : Measure LoopPlane) →L[ℝ]
      Lp E 2 ((volume.restrict (Icc ε R)).prod (volume.restrict (Icc (-Real.pi) Real.pi))) :=
  ChartLpNative.dominatedPullbackL2 (polarPlane x)
    (polarPlane_measurePreserving x).measurable.aemeasurable
    (ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr hε)))
    (polarPlane_map_strip_le x hε)



theorem polarPullbackL2_ae (x : LoopPlane) {ε : ℝ} (R : ℝ) (hε : 0 < ε)
    (u : Lp E 2 (volume : Measure LoopPlane)) :
    polarPullbackL2 x R hε u =ᵐ[
      (volume.restrict (Icc ε R)).prod (volume.restrict (Icc (-Real.pi) Real.pi))]
        fun p => u (polarPlane x p) :=
  ChartLpNative.dominatedPullbackL2_coe _ _ _ _ u

private def angularCoefficient (i : Fin 2) (p : ℝ × ℝ) : ℝ :=
  if i = 0 then -p.1 * Real.sin p.2 else p.1 * Real.cos p.2

private theorem continuous_angularCoefficient (i : Fin 2) : Continuous (angularCoefficient i) := by
  change Continuous (fun p : ℝ × ℝ =>
    if i = 0 then -p.1 * Real.sin p.2 else p.1 * Real.cos p.2)
  split_ifs <;> fun_prop

private theorem angularCoefficient_bound {ε R : ℝ} (hε : 0 < ε) (i : Fin 2) :
    ∀ᵐ p ∂((volume.restrict (Icc ε R)).prod (volume.restrict (Icc (-Real.pi) Real.pi))),
      ‖angularCoefficient i p‖ ≤ R := by
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
  have hr : 0 ≤ p.1 := (hε.trans_le hp.1.1).le
  by_cases hi : i = 0
  · simp only [angularCoefficient, if_pos hi, norm_mul, norm_neg,
      Real.norm_eq_abs, abs_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one p.2) hr).trans
      (by simpa only [mul_one] using hp.1.2)
  · simp only [angularCoefficient, if_neg hi, norm_mul,
      Real.norm_eq_abs, abs_of_nonneg hr]
    exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one p.2) hr).trans
      (by simpa only [mul_one] using hp.1.2)

private def angularMultiplierL2 {ε : ℝ} (R : ℝ) (hε : 0 < ε) (i : Fin 2) :
    Lp ℝ 2 ((volume.restrict (Icc ε R)).prod (volume.restrict (Icc (-Real.pi) Real.pi))) →L[ℝ]
      Lp ℝ 2 ((volume.restrict (Icc ε R)).prod (volume.restrict (Icc (-Real.pi) Real.pi))) :=
  Lp.coefficientL2 (fun p => angularCoefficient i p • ContinuousLinearMap.id ℝ ℝ)
    ((continuous_angularCoefficient i).smul continuous_const).aestronglyMeasurable R
    (by
      filter_upwards [angularCoefficient_bound (R := R) hε i] with p hp
      simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using hp)

private theorem angularMultiplierL2_ae {ε : ℝ} (R : ℝ) (hε : 0 < ε) (i : Fin 2)
    (u : Lp ℝ 2 ((volume.restrict (Icc ε R)).prod
      (volume.restrict (Icc (-Real.pi) Real.pi)))) :
    angularMultiplierL2 R hε i u =ᵐ[
      (volume.restrict (Icc ε R)).prod (volume.restrict (Icc (-Real.pi) Real.pi))]
        fun p => angularCoefficient i p * u p := by
  exact Lp.coefficientL2_ae _ _ _ _ u




def polarAngularL2 (x : LoopPlane) {ε : ℝ} (R : ℝ) (hε : 0 < ε) :
    (Fin 2 → Lp ℝ 2 (volume : Measure LoopPlane)) →L[ℝ]
      Lp ℝ 2 ((volume.restrict (Icc ε R)).prod (volume.restrict (Icc (-Real.pi) Real.pi))) :=
  ((angularMultiplierL2 R hε 0).comp (polarPullbackL2 x R hε)).comp
      (ContinuousLinearMap.proj 0) +
    ((angularMultiplierL2 R hε 1).comp (polarPullbackL2 x R hε)).comp
      (ContinuousLinearMap.proj 1)




theorem polarAngularL2_ae (x : LoopPlane) {ε : ℝ} (R : ℝ) (hε : 0 < ε)
    (d : Fin 2 → Lp ℝ 2 (volume : Measure LoopPlane)) :
    polarAngularL2 x R hε d =ᵐ[
      (volume.restrict (Icc ε R)).prod (volume.restrict (Icc (-Real.pi) Real.pi))]
        fun p => -p.1 * Real.sin p.2 * d 0 (polarPlane x p) +
          p.1 * Real.cos p.2 * d 1 (polarPlane x p) := by
  let a := angularMultiplierL2 R hε 0 (polarPullbackL2 x R hε (d 0))
  let b := angularMultiplierL2 R hε 1 (polarPullbackL2 x R hε (d 1))
  change (a + b : Lp ℝ 2 _) =ᵐ[_] _
  filter_upwards [Lp.coeFn_add a b,
    angularMultiplierL2_ae R hε 0 (polarPullbackL2 x R hε (d 0)),
    angularMultiplierL2_ae R hε 1 (polarPullbackL2 x R hε (d 1)),
    polarPullbackL2_ae x R hε (d 0), polarPullbackL2_ae x R hε (d 1)]
    with p hp ha hb hd0 hd1
  rw [hp]
  change a p + b p = _
  rw [ha, hb, hd0, hd1]
  simp [angularCoefficient]

end PoincareConjecture.M65Interior
