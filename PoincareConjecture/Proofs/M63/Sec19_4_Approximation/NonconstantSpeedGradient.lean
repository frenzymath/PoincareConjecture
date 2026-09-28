import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.C2TraceSpeedGradient

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle intervalIntegral Topology

universe u

namespace PoincareConjecture.M63

open M62

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem curveSpeed_spatial_ratio_integral_of_speed_le [T2Space M]
    (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
    (hc : M62ShrinkingCurve F c) {K R J V : ℝ}
    (hK : 0 ≤ K) (hR : 0 ≤ R) (hJ : 0 ≤ J) (hV : 0 ≤ V)
    (hBounds : CurveEvolutionAmbientBounds F K K K)
    (hSpeed : ∀ r ∈ Ioo a b, ∀ y, curveSpeed F c r y ≤ V)
    (hCurv : ∀ r ∈ Ioo a b, ∀ y, m62CurvatureSquared F c r y ≤ R)
    (hJet : ∀ r ∈ Ioo a b, ∀ y,
      (F.metric r).tangentNorm (c y r) (m63CurvatureJet F c 1 r y) ≤
        J / Real.sqrt (r - a))
    {t : ℝ} (ht : t ∈ Icc a b) (x : ℝ) :
    IntervalIntegrable
      (fun r => deriv (fun y =>
        m62TangentRicci F c r y + m62CurvatureSquared F c r y) x) volume a t ∧
    deriv (curveSpeed F c t) x / curveSpeed F c t x =
      deriv (curveSpeed F c a) x / curveSpeed F c a x -
        (∫ r in a..t, deriv (fun y =>
          m62TangentRicci F c r y + m62CurvatureSquared F c r y) x) ∧
    |deriv (curveSpeed F c t) x / curveSpeed F c t x -
        deriv (curveSpeed F c a) x / curveSpeed F c a x| ≤
      V * ((K + 2 * K * Real.sqrt R) * (t - a) +
        4 * Real.sqrt R * J * Real.sqrt (t - a)) := by
  let A : ℝ × ℝ → ℝ := fun z =>
    m62TangentRicci F c z.2 z.1 + m62CurvatureSquared F c z.2 z.1
  let Ax : ℝ × ℝ → ℝ := M08.coordinatePartialS A
  let B : ℝ → ℝ := fun r => V * (K + 2 * K * Real.sqrt R) +
    (2 * V * Real.sqrt R * J) * (r - a) ^ (-(1 / 2 : ℝ))
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
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
    have hnorm : 0 ≤ (F.metric r).tangentNorm (c y r)
        (m63CurvatureJet F c 1 r y) := Real.sqrt_nonneg _
    have hco : K + 2 * K * m62Curvature F c r y +
        2 * m62Curvature F c r y *
          (F.metric r).tangentNorm (c y r) (m63CurvatureJet F c 1 r y) ≤
        K + 2 * K * Real.sqrt R + 2 * Real.sqrt R * (J / Real.sqrt (r - a)) := by
      apply add_le_add
      · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hk
          (show 0 ≤ 2 * K by positivity))
      · exact (mul_le_mul_of_nonneg_left (hJet r hr y) (by positivity)).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by norm_num)) hu)
    have hco0 : 0 ≤ K + 2 * K * m62Curvature F c r y +
        2 * m62Curvature F c r y *
          (F.metric r).tangentNorm (c y r) (m63CurvatureJet F c 1 r y) := by positivity
    have hp : (r - a) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (r - a))⁻¹ := by
      rw [Real.rpow_neg (sub_nonneg.mpr hr.1.le), ← Real.sqrt_eq_rpow]
    rw [Real.norm_eq_abs, ← (hdiff r hr y).deriv]
    calc
      _ ≤ curveSpeed F c r y *
          (K + 2 * K * m62Curvature F c r y + 2 * m62Curvature F c r y *
            (F.metric r).tangentNorm (c y r) (m63CurvatureJet F c 1 r y)) :=
        normalizationCoefficient_spatial_abs_bound F c hc hBounds hr y
      _ ≤ V * (K + 2 * K * Real.sqrt R +
          2 * Real.sqrt R * (J / Real.sqrt (r - a))) :=
        mul_le_mul (hSpeed r hr y) hco hco0 hV
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
  have hEq : EqOn (fun r => Ax (x, r))
      (fun r => deriv (fun y =>
        m62TangentRicci F c r y + m62CurvatureSquared F c r y) x) (uIoo a t) := by
    intro r hr
    rw [uIoo_of_le ht.1] at hr
    exact (hdiff r ⟨hr.1, hr.2.trans_le ht.2⟩ x).deriv.symm
  have hI := intervalIntegral.integral_congr_uIoo (μ := volume) hEq
  have heq (y : ℝ) : Real.log (curveSpeed F c t y) =
      Real.log (curveSpeed F c a y) - ∫ r in a..t, A (y, r) :=
    curveSpeed_log_eq_integral F c hc hBounds y
      (fun r hr => hCurv r hr y) ha ht ht.1
  have hloga := ((speed_contDiff F c hc ha).differentiable (by norm_num) x).hasDerivAt.log
    (speed_pos F c hc ha x).ne'
  have hlogt := ((speed_contDiff F c hc ht).differentiable (by norm_num) x).hasDerivAt.log
    (speed_pos F c hc ht x).ne'
  have hlog' := (hloga.sub hderiv.2).congr_of_eventuallyEq (Eventually.of_forall heq)
  have hformula := hlogt.unique hlog'
  rw [hI] at hformula
  refine ⟨hderiv.1.congr_uIoo hEq, hformula, ?_⟩
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
  have hIbound := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun r => Ax (x, r)) ht.1 (by
      filter_upwards [volume.ae_ne t] with r hrt
      intro hr
      exact hbound r ⟨hr.1, (lt_of_le_of_ne hr.2 hrt).trans_le ht.2⟩ x) hB
  rw [hBI, hI, Real.norm_eq_abs] at hIbound
  calc
    _ = |-(∫ r in a..t, deriv (fun y =>
        m62TangentRicci F c r y + m62CurvatureSquared F c r y) x)| := by
      rw [hformula]
      congr 1
      ring
    _ = _ := abs_neg _
    _ ≤ _ := hIbound

end PoincareConjecture.M63
