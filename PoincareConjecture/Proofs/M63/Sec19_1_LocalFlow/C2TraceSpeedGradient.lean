import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceSpeed
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceNormalization
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic











set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle intervalIntegral Topology

universe u

namespace PoincareConjecture.M63

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}





theorem curveSpeed_spatial_derivative_integral [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {K R J v0 : ℝ}
    (hK : 0 ≤ K) (hR : 0 ≤ R) (hJ : 0 ≤ J) (hv0 : 0 < v0)
    (hBounds : CurveEvolutionAmbientBounds F K K K)
    (hInitial : ∀ y, curveSpeed F c a y = v0)
    (hCurv : ∀ r ∈ Ioo a b, ∀ y, m62CurvatureSquared F c r y ≤ R)
    (hJet : ∀ r ∈ Ioo a b, ∀ y,
      (F.metric r).tangentNorm (c y r) (m63CurvatureJet F c 1 r y) ≤
        J / Real.sqrt (r - a))
    {t : ℝ} (ht : t ∈ Icc a b) (x : ℝ) :
    deriv (curveSpeed F c t) x = -curveSpeed F c t x *
      ∫ r in a..t,
        deriv (fun y => m62TangentRicci F c r y + m62CurvatureSquared F c r y) x := by
  let V := v0 * Real.exp ((K + R) * (b - a))
  let A : ℝ × ℝ → ℝ := fun z =>
    m62TangentRicci F c z.2 z.1 + m62CurvatureSquared F c z.2 z.1
  let Ax : ℝ × ℝ → ℝ := M08.coordinatePartialS A
  let B : ℝ → ℝ := fun r => V * (K + 2 * K * Real.sqrt R) +
    (2 * V * Real.sqrt R * J) * (r - a) ^ (-(1 / 2 : ℝ))
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have hV (r : ℝ) (hr : r ∈ Icc a b) (y : ℝ) : curveSpeed F c r y ≤ V := by
    have h := (curveSpeed_exp_bounds F c hc hBounds y
      (fun s hs => hCurv s hs y) ha hr hr.1).2
    rw [hInitial] at h
    exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hr.2 a) (add_nonneg hK hR))) hv0.le)
  have hopen : IsOpen (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := isOpen_univ.prod isOpen_Ioo
  have hA : ContDiffOn ℝ ∞ A (univ ×ˢ Ioo a b) :=
    normalization_coefficient_contDiffOn F c hc
  have hAx : ContDiffOn ℝ ∞ Ax (univ ×ˢ Ioo a b) :=
    M08.coordinatePartialS_contDiffOn hopen A hA
  have hdiff (r : ℝ) (hr : r ∈ Ioo a b) (y : ℝ) :
      HasDerivAt (fun y => A (y, r)) (Ax (y, r)) y := by
    have hmem : (y, r) ∈ (univ ×ˢ Ioo a b : Set (ℝ × ℝ)) := ⟨mem_univ _, hr⟩
    have hd : DifferentiableAt ℝ A (y, r) :=
      (hA.contDiffAt (hopen.mem_nhds hmem)).differentiableAt (by simp)
    exact M08.coordinateSlice_fst_hasDerivAt A (p := (y, r)) hd
  have hbound (r : ℝ) (hr : r ∈ Ioo a b) (y : ℝ) : ‖Ax (y, r)‖ ≤ B r := by
    have hk0 := curvature_nonneg F c r y
    have hk : m62Curvature F c r y ≤ Real.sqrt R := by
      nlinarith only [curvature_sq F c r y, hCurv r hr y,
        Real.sq_sqrt hR, Real.sqrt_nonneg R]
    have hu : 0 ≤ J / Real.sqrt (r - a) := div_nonneg hJ (Real.sqrt_nonneg _)
    have hco : K + 2 * K * m62Curvature F c r y +
        2 * m62Curvature F c r y *
          (F.metric r).tangentNorm (c y r) (m63CurvatureJet F c 1 r y) ≤
        K + 2 * K * Real.sqrt R + 2 * Real.sqrt R * (J / Real.sqrt (r - a)) := by
      apply add_le_add
      · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hk
          (show 0 ≤ 2 * K by positivity))
      · exact (mul_le_mul_of_nonneg_left (hJet r hr y) (by positivity)).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by norm_num)) hu)
    have hco0 : 0 ≤ K + 2 * K * Real.sqrt R +
        2 * Real.sqrt R * (J / Real.sqrt (r - a)) := by positivity
    have hp : (r - a) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (r - a))⁻¹ := by
      rw [Real.rpow_neg (sub_nonneg.mpr hr.1.le), ← Real.sqrt_eq_rpow]
    rw [Real.norm_eq_abs, ← (hdiff r hr y).deriv]
    calc
      _ ≤ curveSpeed F c r y *
          (K + 2 * K * m62Curvature F c r y + 2 * m62Curvature F c r y *
            (F.metric r).tangentNorm (c y r) (m63CurvatureJet F c 1 r y)) :=
        normalizationCoefficient_spatial_abs_bound F c hc hBounds hr y
      _ ≤ curveSpeed F c r y *
          (K + 2 * K * Real.sqrt R + 2 * Real.sqrt R * (J / Real.sqrt (r - a))) :=
        mul_le_mul_of_nonneg_left hco (speed_nonneg F c r y)
      _ ≤ V * (K + 2 * K * Real.sqrt R +
          2 * Real.sqrt R * (J / Real.sqrt (r - a))) :=
        mul_le_mul_of_nonneg_right (hV r (Ioo_subset_Icc_self hr) y) hco0
      _ = B r := by dsimp only [B]; rw [hp]; ring
  have hpow : IntervalIntegrable (fun r : ℝ => (r - a) ^ (-(1 / 2 : ℝ))) volume a t := by
    simpa only [zero_add, sub_add_cancel] using
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t - a)
        (r := -(1 / 2 : ℝ)) (by norm_num)).comp_sub_right a
  have hB : IntervalIntegrable B volume a t :=
    intervalIntegrable_const.add (hpow.const_mul _)
  have hAint (y : ℝ) : IntervalIntegrable (fun r => A (y, r)) volume a t :=
    normalizationCoefficient_intervalIntegrable F c hc hBounds y
      (fun r hr => hCurv r hr y) ha ht ht.1
  have hAxmeas : AEStronglyMeasurable (fun r => Ax (x, r))
      (volume.restrict (uIoc a t)) := by
    rw [uIoc_of_le ht.1, ← restrict_Ioo_eq_restrict_Ioc]
    have hslice : Continuous (fun r : ℝ => (x, r)) := continuous_const.prodMk continuous_id
    have hmaps : MapsTo (fun r : ℝ => (x, r)) (Ioo a t) (univ ×ˢ Ioo a b) := by
      intro r hr
      exact ⟨mem_univ _, hr.1, hr.2.trans_le ht.2⟩
    have hcont : ContinuousOn (fun r => Ax (x, r)) (Ioo a t) := by
      simpa only [Function.comp_def] using hAx.continuousOn.comp hslice.continuousOn hmaps
    exact hcont.aestronglyMeasurable measurableSet_Ioo
  have hderiv := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y r => A (y, r)) (F' := fun y r => Ax (y, r))
    (x₀ := x) (s := univ) (bound := B) (a := a) (b := t)
    (by simp) (Eventually.of_forall fun y => (hAint y).def'.aestronglyMeasurable)
    (hAint x) hAxmeas (by
      filter_upwards [volume.ae_ne t] with r hrt
      intro hr y _
      rw [uIoc_of_le ht.1] at hr
      exact hbound r ⟨hr.1, (lt_of_le_of_ne hr.2 hrt).trans_le ht.2⟩ y)
    hB (by
      filter_upwards [volume.ae_ne t] with r hrt
      intro hr y _
      rw [uIoc_of_le ht.1] at hr
      exact hdiff r ⟨hr.1, (lt_of_le_of_ne hr.2 hrt).trans_le ht.2⟩ y)
  have heq (y : ℝ) : Real.log (curveSpeed F c t y) =
      Real.log v0 - ∫ r in a..t, A (y, r) := by
    rw [curveSpeed_log_eq_integral F c hc hBounds y
      (fun r hr => hCurv r hr y) ha ht ht.1, hInitial]
  have hlog := ((speed_contDiff F c hc ht).differentiable (by norm_num) x).hasDerivAt.log
    (speed_pos F c hc ht x).ne'
  have hlog' := (hderiv.2.const_sub (Real.log v0)).congr_of_eventuallyEq
    (Eventually.of_forall heq)
  have hI : (∫ r in a..t, Ax (x, r)) =
      ∫ r in a..t,
        deriv (fun y => m62TangentRicci F c r y + m62CurvatureSquared F c r y) x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne t] with r hrt
    intro hr
    rw [uIoc_of_le ht.1] at hr
    exact (hdiff r ⟨hr.1, (lt_of_le_of_ne hr.2 hrt).trans_le ht.2⟩ x).deriv.symm
  have hid := hlog.unique hlog'
  rw [hI] at hid
  exact (div_eq_iff (speed_pos F c hc ht x).ne').mp hid |>.trans (by ring)





theorem curveSpeed_spatial_abs_bound [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {K R J v0 : ℝ}
    (hK : 0 ≤ K) (hR : 0 ≤ R) (hJ : 0 ≤ J) (hv0 : 0 < v0)
    (hBounds : CurveEvolutionAmbientBounds F K K K)
    (hInitial : ∀ y, curveSpeed F c a y = v0)
    (hCurv : ∀ r ∈ Ioo a b, ∀ y, m62CurvatureSquared F c r y ≤ R)
    (hJet : ∀ r ∈ Ioo a b, ∀ y,
      (F.metric r).tangentNorm (c y r) (m63CurvatureJet F c 1 r y) ≤
        J / Real.sqrt (r - a))
    {t : ℝ} (ht : t ∈ Icc a b) (x : ℝ) :
    |deriv (curveSpeed F c t) x| ≤ (v0 * Real.exp ((K + R) * (b - a))) ^ 2 *
      ((K + 2 * K * Real.sqrt R) * (t - a) +
        4 * Real.sqrt R * J * Real.sqrt (t - a)) := by
  let V := v0 * Real.exp ((K + R) * (b - a))
  let B : ℝ → ℝ := fun r => V * (K + 2 * K * Real.sqrt R) +
    (2 * V * Real.sqrt R * J) * (r - a) ^ (-(1 / 2 : ℝ))
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have hV0 : 0 ≤ V := (mul_pos hv0 (Real.exp_pos _)).le
  have hV (r : ℝ) (hr : r ∈ Icc a b) (y : ℝ) : curveSpeed F c r y ≤ V := by
    have h := (curveSpeed_exp_bounds F c hc hBounds y
      (fun s hs => hCurv s hs y) ha hr hr.1).2
    rw [hInitial] at h
    exact h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hr.2 a) (add_nonneg hK hR))) hv0.le)
  have hbound (r : ℝ) (hr : r ∈ Ioo a b) :
      ‖deriv (fun y => m62TangentRicci F c r y + m62CurvatureSquared F c r y) x‖ ≤ B r := by
    have hk0 := curvature_nonneg F c r x
    have hk : m62Curvature F c r x ≤ Real.sqrt R := by
      nlinarith only [curvature_sq F c r x, hCurv r hr x,
        Real.sq_sqrt hR, Real.sqrt_nonneg R]
    have hu : 0 ≤ J / Real.sqrt (r - a) := div_nonneg hJ (Real.sqrt_nonneg _)
    have hco : K + 2 * K * m62Curvature F c r x +
        2 * m62Curvature F c r x *
          (F.metric r).tangentNorm (c x r) (m63CurvatureJet F c 1 r x) ≤
        K + 2 * K * Real.sqrt R + 2 * Real.sqrt R * (J / Real.sqrt (r - a)) := by
      apply add_le_add
      · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hk
          (show 0 ≤ 2 * K by positivity))
      · exact (mul_le_mul_of_nonneg_left (hJet r hr x) (by positivity)).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by norm_num)) hu)
    have hco0 : 0 ≤ K + 2 * K * Real.sqrt R +
        2 * Real.sqrt R * (J / Real.sqrt (r - a)) := by positivity
    have hp : (r - a) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (r - a))⁻¹ := by
      rw [Real.rpow_neg (sub_nonneg.mpr hr.1.le), ← Real.sqrt_eq_rpow]
    rw [Real.norm_eq_abs]
    calc
      _ ≤ curveSpeed F c r x *
          (K + 2 * K * m62Curvature F c r x + 2 * m62Curvature F c r x *
            (F.metric r).tangentNorm (c x r) (m63CurvatureJet F c 1 r x)) :=
        normalizationCoefficient_spatial_abs_bound F c hc hBounds hr x
      _ ≤ curveSpeed F c r x *
          (K + 2 * K * Real.sqrt R + 2 * Real.sqrt R * (J / Real.sqrt (r - a))) :=
        mul_le_mul_of_nonneg_left hco (speed_nonneg F c r x)
      _ ≤ V * (K + 2 * K * Real.sqrt R +
          2 * Real.sqrt R * (J / Real.sqrt (r - a))) :=
        mul_le_mul_of_nonneg_right (hV r (Ioo_subset_Icc_self hr) x) hco0
      _ = B r := by dsimp only [B]; rw [hp]; ring
  have hpow : IntervalIntegrable (fun r : ℝ => (r - a) ^ (-(1 / 2 : ℝ))) volume a t := by
    simpa only [zero_add, sub_add_cancel] using
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t - a)
        (r := -(1 / 2 : ℝ)) (by norm_num)).comp_sub_right a
  have hB : IntervalIntegrable B volume a t :=
    intervalIntegrable_const.add (hpow.const_mul _)
  have hpowI : (∫ r in a..t, (r - a) ^ (-(1 / 2 : ℝ))) = 2 * Real.sqrt (t - a) := by
    rw [intervalIntegral.integral_comp_sub_right
      (f := fun r : ℝ => r ^ (-(1 / 2 : ℝ))) a, sub_self,
      integral_rpow (Or.inl (by norm_num))]
    norm_num [← Real.sqrt_eq_rpow]
    ring
  have hBI : (∫ r in a..t, B r) = V *
      ((K + 2 * K * Real.sqrt R) * (t - a) +
        4 * Real.sqrt R * J * Real.sqrt (t - a)) := by
    dsimp only [B]
    rw [intervalIntegral.integral_add intervalIntegrable_const (hpow.const_mul _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, hpowI]
    simp only [smul_eq_mul]
    ring
  have hI := intervalIntegral.norm_integral_le_of_norm_le (f := fun r =>
    deriv (fun y => m62TangentRicci F c r y + m62CurvatureSquared F c r y) x)
    ht.1 (by
      filter_upwards [volume.ae_ne t] with r hrt
      intro hr
      exact hbound r ⟨hr.1, (lt_of_le_of_ne hr.2 hrt).trans_le ht.2⟩) hB
  rw [hBI, Real.norm_eq_abs] at hI
  rw [curveSpeed_spatial_derivative_integral F c hc hK hR hJ hv0
    hBounds hInitial hCurv hJet ht x, abs_mul, abs_neg,
    abs_of_pos (speed_pos F c hc ht x)]
  calc
    _ ≤ V * |∫ r in a..t,
        deriv (fun y => m62TangentRicci F c r y + m62CurvatureSquared F c r y) x| :=
      mul_le_mul_of_nonneg_right (hV t ht x) (abs_nonneg _)
    _ ≤ V * (V * ((K + 2 * K * Real.sqrt R) * (t - a) +
        4 * Real.sqrt R * J * Real.sqrt (t - a))) :=
      mul_le_mul_of_nonneg_left hI hV0
    _ = _ := by dsimp only [V]; ring

end PoincareConjecture.M63
