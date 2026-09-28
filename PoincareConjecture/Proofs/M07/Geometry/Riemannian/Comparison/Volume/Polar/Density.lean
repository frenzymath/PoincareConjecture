import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Polar.ChangeOfVariables
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Polar.Integral

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in

theorem continuousAt_pullbackVolumeDensity_of_contMDiffAt
    (g : RiemannianMetric n M) {f : EuclideanSpace ℝ (Fin n) → M}
    {x : EuclideanSpace ℝ (Fin n)} (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x) :
    ContinuousAt (g.pullbackVolumeDensity f) x := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hG : ContinuousAt (fun y => Matrix.of (fun i j : Fin n => g.inner (f y)
      (mfderiv (𝓡 n) (𝓡 n) f y (b i)) (mfderiv (𝓡 n) (𝓡 n) f y (b j)))) x := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    exact (g.contDiffAt_pullback_inner hf (b i) (b j)).continuousAt
  exact Real.continuous_sqrt.continuousAt.comp
    (continuous_id.matrix_det.continuousAt.comp hG)

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] in

theorem measurable_indicator_pullbackVolumeDensity
    (g : RiemannianMetric n M) {f : EuclideanSpace ℝ (Fin n) → M}
    {U s : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hs : MeasurableSet s) (hsU : s ⊆ U) :
    Measurable (s.indicator (fun x => ENNReal.ofReal (g.pullbackVolumeDensity f x))) := by
  classical
  let ρ : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
    fun x => ENNReal.ofReal (g.pullbackVolumeDensity f x)
  have hρ : ContinuousOn ρ U := fun x hx =>
    (ENNReal.continuous_ofReal.continuousAt.comp
      (g.continuousAt_pullbackVolumeDensity_of_contMDiffAt
        (hf.contMDiffAt (hU.mem_nhds hx)))).continuousWithinAt
  have hm : Measurable (U.piecewise ρ 0) :=
    ContinuousOn.measurable_piecewise hρ continuousOn_const hU.measurableSet
  convert hm.indicator hs using 1
  ext x
  by_cases hx : x ∈ s
  · simp only [indicator_of_mem hx, piecewise_eq_of_mem _ _ _ (hsU hx)]
    rfl
  · simp only [indicator_of_notMem hx]

theorem volumeMeasure_image_inter_ball_eq_polar
    (g : RiemannianMetric n M) (hn : 1 ≤ n)
    {f : EuclideanSpace ℝ (Fin n) → M}
    {U s : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hs : MeasurableSet s) (hsU : s ⊆ U) (hinj : InjOn f s) (r : ℝ) :
    g.volumeMeasure (f '' (s ∩ Metric.ball 0 r)) =
      ∫⁻ θ : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (∫⁻ t in Ioo (0 : ℝ) r, ENNReal.ofReal (t ^ (n - 1)) *
          s.indicator (fun x => ENNReal.ofReal (g.pullbackVolumeDensity f x))
            (t • (θ : EuclideanSpace ℝ (Fin n)))) ∂volume.toSphere := by
  have : NeZero n := ⟨by omega⟩
  rw [g.volumeMeasure_image_eq_lintegral_of_mdifferentiableAt_injOn
    (hs.inter Metric.isOpen_ball.measurableSet)
    (fun x hx => (hf.contMDiffAt (hU.mem_nhds (hsU hx.1))).mdifferentiableAt (by simp))
    (hinj.mono inter_subset_left)]
  have hpolar := Poincare.VolumeComparison.setLIntegral_ball_eq_polar
    (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (g.measurable_indicator_pullbackVolumeDensity hU hf hs hsU) r
  rw [lintegral_indicator hs, Measure.restrict_restrict hs] at hpolar
  simpa only [finrank_euclideanSpace_fin] using hpolar

end PoincareConjecture.RiemannianMetric
