import PoincareConjecture.Proofs.M36.RadialArclength









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal
open MeasureTheory

namespace PoincareConjecture.M36

theorem axisPoint_hasDerivAt (r : ℝ) : HasDerivAt axisPoint (axisBasis 0) r := by
  rw [show axisPoint = fun t => t • axisBasis 0 from funext axisPoint_eq_smul]
  convert! (hasDerivAt_id r).smul_const (axisBasis 0) using 1
  simp

theorem axisPoint_mfderiv_one (r : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 3) axisPoint r 1 = axisBasis 0 := by
  rw [mfderiv_eq_fderiv, (axisPoint_hasDerivAt r).hasFDerivAt.fderiv]
  change (1 : ℝ) • axisBasis 0 = axisBasis 0
  exact one_smul ℝ (axisBasis 0)

theorem axis_pathELength (g₀ : StandardInitialMetric) {a b : ℝ} (hab : a ≤ b) :
    g₀.metric.pathELength axisPoint a b =
      ENNReal.ofReal (radialArclength g₀ b - radialArclength g₀ a) := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
    ⟨g₀.metric.toRiemannianMetric⟩
  have hc := (radialSpeed_contDiff g₀).continuous
  change Manifold.pathELength (𝓡 3) axisPoint a b = _
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  calc
    _ = ∫⁻ t in Set.Icc a b, ENNReal.ofReal (radialSpeed g₀ t) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t _
      dsimp only
      erw [← ofReal_norm, norm_eq_sqrt_real_inner]
      change ENNReal.ofReal (Real.sqrt (g₀.metric.inner (axisPoint t)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) axisPoint t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) axisPoint t 1))) = _
      rw [axisPoint_mfderiv_one]
      rfl
    _ = ENNReal.ofReal (∫ t in Set.Icc a b, radialSpeed g₀ t) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal hc.integrableOn_Icc
        (Filter.Eventually.of_forall fun t => (radialSpeed_pos g₀ t).le)
    _ = ENNReal.ofReal (∫ t in a..b, radialSpeed g₀ t) := by
      rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
    _ = _ := by
      congr 1
      exact (intervalIntegral.integral_interval_sub_left
        (hc.intervalIntegrable 0 b) (hc.intervalIntegrable 0 a)).symm

theorem axis_edist_le_arclength_sub (g₀ : StandardInitialMetric)
    {a b : ℝ} (hab : a ≤ b) :
    g₀.metric.edist (axisPoint a) (axisPoint b) ≤
      ENNReal.ofReal (radialArclength g₀ b - radialArclength g₀ a) := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
    ⟨g₀.metric.toRiemannianMetric⟩
  have hp : g₀.metric.edist (axisPoint a) (axisPoint b) ≤
      g₀.metric.pathELength axisPoint a b :=
    Manifold.riemannianEDist_le_pathELength
      (axisPoint_contDiff.contMDiff.of_le (by norm_num)).contMDiffOn rfl rfl hab
  exact hp.trans_eq (axis_pathELength g₀ hab)

theorem axis_edist_le_arclength_edist (g₀ : StandardInitialMetric) (a b : ℝ) :
    g₀.metric.edist (axisPoint a) (axisPoint b) ≤
      edist (radialArclength g₀ a) (radialArclength g₀ b) := by
  have hmono := (radialArclength_strictMono g₀).monotone
  rcases le_total a b with hab | hba
  · rw [edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hmono hab)), neg_sub]
    exact axis_edist_le_arclength_sub g₀ hab
  · let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
      ⟨g₀.metric.toRiemannianMetric⟩
    have hcomm : g₀.metric.edist (axisPoint a) (axisPoint b) =
        g₀.metric.edist (axisPoint b) (axisPoint a) := Manifold.riemannianEDist_comm
    rw [hcomm, edist_dist, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hmono hba))]
    exact axis_edist_le_arclength_sub g₀ hba

end PoincareConjecture.M36
