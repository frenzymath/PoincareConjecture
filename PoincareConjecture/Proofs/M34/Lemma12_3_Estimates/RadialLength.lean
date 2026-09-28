import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.RadialForm
import PoincareConjecture.Proofs.M09.RiemannianProper
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.MetricComparison
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false

open Set MeasureTheory Manifold
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.M34

noncomputable def initialRadialSpeed (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  Real.sqrt (initialRadialCoefficient g₀ r)

noncomputable def initialWarping (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  r * Real.sqrt (initialAngularCoefficient g₀ r)

theorem initialRadialSpeed_pos (g₀ : StandardInitialMetric) (r : ℝ) :
    0 < initialRadialSpeed g₀ r := Real.sqrt_pos.mpr (initialCoefficients_pos g₀ r).1

theorem initialRadialSpeed_contDiff (g₀ : StandardInitialMetric) :
    ContDiff ℝ ∞ (initialRadialSpeed g₀) :=
  (initialRadialCoefficient_contDiff g₀).sqrt (fun r => (initialCoefficients_pos g₀ r).1.ne')

theorem initialWarping_contDiff (g₀ : StandardInitialMetric) :
    ContDiff ℝ ∞ (initialWarping g₀) :=
  contDiff_id.mul ((initialAngularCoefficient_contDiff g₀).sqrt
    (fun r => (initialCoefficients_pos g₀ r).2.ne'))

theorem initialWarping_pos (g₀ : StandardInitialMetric) {r : ℝ} (hr : 0 < r) :
    0 < initialWarping g₀ r :=
  mul_pos hr (Real.sqrt_pos.mpr (initialCoefficients_pos g₀ r).2)

noncomputable def initialRadialLength (g₀ : StandardInitialMetric) (r : ℝ) : ℝ :=
  ∫ t in 0..r, initialRadialSpeed g₀ t

theorem initialRadialLength_hasDerivAt (g₀ : StandardInitialMetric) (r : ℝ) :
    HasDerivAt (initialRadialLength g₀) (initialRadialSpeed g₀ r) r := by
  have hc := (initialRadialSpeed_contDiff g₀).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

set_option backward.isDefEq.respectTransparency false in

theorem initialAxis_edist_le_radialLength (g₀ : StandardInitialMetric)
    {r : ℝ} (hr : 0 ≤ r) :
    g₀.metric.edist 0 (EuclideanSpace.single (0 : Fin 3) r) ≤
      ENNReal.ofReal (initialRadialLength g₀ r) := by
  let v : StandardCapSpace := EuclideanSpace.single 0 1
  let γ : ℝ → StandardCapSpace := fun t => t • v
  have hγ : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) 1 γ :=
    contMDiff_iff_contDiff.mpr (contDiff_id.smul contDiff_const)
  have hd (t : ℝ) : mfderiv (𝓘(ℝ, ℝ)) (𝓡 3) γ t 1 = v := by
    rw [mfderiv_eq_fderiv]
    have h : HasDerivAt γ v t := by
      simpa [γ] using (hasDerivAt_id t).smul_const v
    rw [h.hasFDerivAt.fderiv]
    exact one_smul ℝ v
  have haxis (t : ℝ) : γ t = EuclideanSpace.single (0 : Fin 3) t := by
    ext i
    simp [γ, v]
  have hlength : g₀.metric.pathELength γ 0 r =
      ENNReal.ofReal (initialRadialLength g₀ r) := by
    rw [RiemannianMetric.pathELength_eq_lintegral_tangentNorm]
    have heq (t : ℝ) : g₀.metric.tangentNorm (γ t)
        (mfderiv (𝓘(ℝ, ℝ)) (𝓡 3) γ t 1) = initialRadialSpeed g₀ t := by
      rw [hd]
      unfold RiemannianMetric.tangentNorm initialRadialSpeed initialRadialCoefficient
      erw [haxis]
    simp_rw [heq]
    unfold initialRadialLength
    rw [intervalIntegral.integral_of_le hr, ← integral_Icc_eq_integral_Ioc]
    exact (ofReal_integral_eq_lintegral_ofReal
      ((initialRadialSpeed_contDiff g₀).continuous.integrableOn_Icc)
      (Filter.Eventually.of_forall (fun t => (initialRadialSpeed_pos g₀ t).le))).symm
  rw [← hlength]
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type) :=
    ⟨g₀.metric.toRiemannianMetric⟩
  exact riemannianEDist_le_pathELength hγ.contMDiffOn
    (by simp [γ]) (haxis r) hr

theorem initialRadialLength_unbounded (g₀ : StandardInitialMetric) (B : ℝ) :
    ∃ r : ℝ, 0 ≤ r ∧ B < initialRadialLength g₀ r := by
  by_contra h
  have hbound : ∀ r : ℝ, 0 ≤ r → initialRadialLength g₀ r ≤ B := by
    intro r hr
    exact le_of_not_gt (fun hb => h ⟨r, hr, hb⟩)
  let K := closure (g₀.metric.ball 0 (max B 0 + 1))
  have hK : IsCompact K := Proofs.M09.isCompact_closure_metric_ball
    g₀.metric g₀.complete 0 (max B 0 + 1)
  obtain ⟨C, hC⟩ := (hK.image continuous_norm).bddAbove
  let r := max C 0 + 1
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hmem : EuclideanSpace.single (0 : Fin 3) r ∈ K := by
    apply subset_closure
    change g₀.metric.edist 0 (EuclideanSpace.single (0 : Fin 3) r) <
      ENNReal.ofReal (max B 0 + 1)
    apply (initialAxis_edist_le_radialLength g₀ hr).trans_lt
    apply (ENNReal.ofReal_le_ofReal (hbound r hr)).trans_lt
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith [le_max_left B 0])
  have hb := hC (mem_image_of_mem (fun x : StandardCapSpace => ‖x‖) hmem)
  have hn : ‖EuclideanSpace.single (0 : Fin 3) r‖ = r := by
    simp [abs_of_nonneg hr]
  rw [hn] at hb
  dsimp [r] at hb
  linarith [le_max_left C 0]

end PoincareConjecture.M34
