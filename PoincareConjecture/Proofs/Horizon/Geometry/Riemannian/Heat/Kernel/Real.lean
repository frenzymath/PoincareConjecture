import PoincareConjecture.Proofs.Horizon.Analysis.Heat.RealKernel
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Transport

set_option autoImplicit false

open MeasureTheory Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

open Poincare.Analysis.Heat

universe u

variable {M : Type u} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M]
  [IsManifold (𝓡 1) ∞ M]

theorem realHeatKernel_first_moment_bound {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (∫ x, |x| * realHeatKernel t x) ≤ Real.sqrt 2 := by
  exact (integral_abs_mul_realHeatKernel_le ht).trans
    (Real.sqrt_le_sqrt (by nlinarith : 2 * t ≤ 2))

theorem tendsto_realHeatKernel_first_moment :
    Tendsto (fun t : ℝ ↦ ∫ x, |x| * realHeatKernel t x) (𝓝[>] 0) (𝓝 0) := by
  have hnonneg : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 ≤ ∫ x, |x| * realHeatKernel t x := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    apply integral_nonneg_of_ae
    filter_upwards [] with x
    change 0 ≤ |x| * realHeatKernel t x
    exact mul_nonneg (abs_nonneg _) (le_of_lt (realHeatKernel_pos ht' x))
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (∫ x, |x| * realHeatKernel t x) ≤ Real.sqrt (2 * t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact integral_abs_mul_realHeatKernel_le ht
  apply squeeze_zero' hnonneg hbound
  have hid : Tendsto (fun t : ℝ ↦ t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hs := (Real.continuous_sqrt.comp
    ((continuous_const : Continuous (fun _ : ℝ ↦ (2 : ℝ))).mul continuous_id)).tendsto 0
  simpa [Function.comp_def] using hs.comp hid

theorem transported_realHeatKernel_mass_one
    (g : RiemannianMetric 1 M) (e : M ≃ ℝ)
    (he : ∀ x y, EDist.edist (e x) (e y) = g.edist x y)
    {t : ℝ} (ht : 0 < t) (x : M) :
    (∫ y, realHeatKernel t (e y - e x) ∂volumeMeasure g) = 1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 1) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 1))
      (TangentSpace (𝓡 1) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 1) M
  let e' : M ≃ᵢ ℝ := ⟨e, he⟩
  have hp := measurePreserving_volumeMeasure_real g e he
  have hcomp := hp.integral_comp e'.toHomeomorph.measurableEmbedding
    (fun z : ℝ ↦ realHeatKernel t (z - e x))
  rw [integral_sub_right_eq_self] at hcomp
  exact hcomp.trans (integral_realHeatKernel ht)

theorem transported_realHeatKernel_pos
    (g : RiemannianMetric 1 M) (e : M ≃ ℝ)
    (_he : ∀ x y, EDist.edist (e x) (e y) = g.edist x y)
    {t : ℝ} (ht : 0 < t) (x y : M) :
    0 < realHeatKernel t (e y - e x) := by
  exact realHeatKernel_pos ht _

theorem transported_realHeatKernel_integrable
    (g : RiemannianMetric 1 M) (e : M ≃ ℝ)
    (he : ∀ x y, EDist.edist (e x) (e y) = g.edist x y)
    {t : ℝ} (ht : 0 < t) (x : M) :
    Integrable (fun y => realHeatKernel t (e y - e x)) (volumeMeasure g) := by
  apply integrable_of_integral_eq_one
  exact transported_realHeatKernel_mass_one g e he ht x

theorem transported_realHeatKernel_timeDifferentiable
    (g : RiemannianMetric 1 M) (e : M ≃ ℝ)
    (_he : ∀ x y, EDist.edist (e x) (e y) = g.edist x y)
    {t : ℝ} (ht : 0 < t) (x y : M) :
    DifferentiableAt ℝ (fun s => realHeatKernel s (e y - e x)) t := by
  exact (hasDerivAt_realHeatKernel_time ht (e y - e x)).differentiableAt

theorem transported_realHeatKernel_first_moment_integrable
    (g : RiemannianMetric 1 M) (e : M ≃ ℝ)
    (he : ∀ x y, EDist.edist (e x) (e y) = g.edist x y)
    {t : ℝ} (ht : 0 < t) (x : M) :
    Integrable (fun y => (g.edist x y).toReal *
      realHeatKernel t (e y - e x)) (volumeMeasure g) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 1) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 1))
      (TangentSpace (𝓡 1) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 1) M
  let e' : M ≃ᵢ ℝ := ⟨e, he⟩
  have hreal : Integrable (fun z : ℝ ↦ |z - e x| *
      realHeatKernel t (z - e x)) := by
    have hshift := (integrable_pow_mul_realHeatKernel ht 1).abs.comp_sub_right (e x)
    convert hshift using 1
    funext z
    rw [abs_mul, abs_of_pos (realHeatKernel_pos ht (z - e x))]
    simp only [pow_one]
  have hp := measurePreserving_volumeMeasure_real g e he
  have hcomp := (hp.integrable_comp_emb e'.toHomeomorph.measurableEmbedding).mpr hreal
  convert hcomp using 1
  funext y
  rw [Function.comp_apply, ← he x y, edist_dist, ENNReal.toReal_ofReal]
  simp [Real.dist_eq, abs_sub_comm]
  exact dist_nonneg

theorem transported_realHeatKernel_first_moment
    (g : RiemannianMetric 1 M) (e : M ≃ ℝ)
    (he : ∀ x y, EDist.edist (e x) (e y) = g.edist x y)
    {t : ℝ} (_ht : 0 < t) (x : M) :
    (∫ y, (g.edist x y).toReal * realHeatKernel t (e y - e x)
      ∂volumeMeasure g) = ∫ z, |z| * realHeatKernel t z := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 1) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 1))
      (TangentSpace (𝓡 1) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 1) M
  let e' : M ≃ᵢ ℝ := ⟨e, he⟩
  have hp := measurePreserving_volumeMeasure_real g e he
  have hpush := hp.integral_comp e'.toHomeomorph.measurableEmbedding
    (fun z : ℝ ↦ |z - e x| * realHeatKernel t (z - e x))
  have hleft :
      (∫ y, (g.edist x y).toReal * realHeatKernel t (e y - e x)
          ∂volumeMeasure g) =
        ∫ y, |e y - e x| * realHeatKernel t (e y - e x)
          ∂volumeMeasure g := by
    apply integral_congr_ae
    filter_upwards [] with y
    rw [← he x y, edist_dist, ENNReal.toReal_ofReal]
    simp [Real.dist_eq, abs_sub_comm]
    exact dist_nonneg
  rw [hleft, hpush]
  simpa using
    (integral_sub_right_eq_self (fun z : ℝ ↦ |z| * realHeatKernel t z) (e x))

theorem transported_realHeatKernel_first_moment_bound
    (g : RiemannianMetric 1 M) (e : M ≃ ℝ)
    (he : ∀ x y, EDist.edist (e x) (e y) = g.edist x y)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (x : M) :
    (∫ y, (g.edist x y).toReal * realHeatKernel t (e y - e x)
      ∂volumeMeasure g) ≤ Real.sqrt 2 := by
  rw [transported_realHeatKernel_first_moment g e he ht x]
  exact realHeatKernel_first_moment_bound ht ht1

theorem transported_realHeatKernel_uniform_first_moment_bound
    (g : RiemannianMetric 1 M) (e : M ≃ ℝ)
    (he : ∀ x y, EDist.edist (e x) (e y) = g.edist x y) :
    ∀ x t, 0 < t → t ≤ 1 →
      (∫ y, (g.edist x y).toReal * realHeatKernel t (e y - e x)
        ∂volumeMeasure g) ≤ Real.sqrt 2 := by
  intro x t ht ht1
  exact transported_realHeatKernel_first_moment_bound g e he ht ht1 x

theorem tendsto_transported_realHeatKernel_first_moment
    (g : RiemannianMetric 1 M) (e : M ≃ ℝ)
    (he : ∀ x y, EDist.edist (e x) (e y) = g.edist x y) :
    Tendsto (fun t ↦ ⨆ x, ∫ y, (g.edist x y).toReal *
      realHeatKernel t (e y - e x) ∂volumeMeasure g)
      (𝓝[>] 0) (𝓝 0) := by
  have : Nonempty M := e.nonempty
  refine (tendsto_congr' ?_).2 tendsto_realHeatKernel_first_moment
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp_rw [transported_realHeatKernel_first_moment g e he ht]
  rw [ciSup_const]

theorem tendsto_gaussianAverage_of_continuous_bounded
    {f : ℝ → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ z, ‖f z‖ ≤ C) (x : ℝ) :
    Tendsto (fun t ↦ gaussianAverage f t x) (𝓝[>] 0) (𝓝 (f x)) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := ProbabilityTheory.gaussianReal 0 1)
    (l := 𝓝[>] (0 : ℝ))
    (F := fun t z : ℝ ↦ f (x + Real.sqrt (2 * t) * z))
    (f := fun _ : ℝ ↦ f x) (fun _ : ℝ ↦ C)
    (Eventually.of_forall (fun t ↦ (hf.comp (by fun_prop)).aestronglyMeasurable))
    (Eventually.of_forall (fun t ↦ ae_of_all _ (fun z ↦ hC _)))
    (integrable_const C) ?_
  · simpa only [gaussianAverage, integral_const, probReal_univ, one_smul] using h
  · apply ae_of_all
    intro z
    have hc : Continuous (fun t : ℝ ↦ f (x + Real.sqrt (2 * t) * z)) := by
      fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

theorem tendsto_transported_realHeatKernel_initial
    (g : RiemannianMetric 1 M) (e : M ≃ ℝ)
    (he : ∀ x y, EDist.edist (e x) (e y) = g.edist x y)
    {φ : M → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) (x : M) :
    Tendsto (fun t ↦ ∫ y, realHeatKernel t (e y - e x) * φ y ∂volumeMeasure g)
      (𝓝[>] 0) (𝓝 (φ x)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 1) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 1))
      (TangentSpace (𝓡 1) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 1) M
  let e' : M ≃ᵢ ℝ := ⟨e, he⟩
  have hp := measurePreserving_volumeMeasure_real g e he
  have hf : Continuous (fun z : ℝ ↦ φ (e.symm z)) :=
    hφ.comp e'.symm.continuous
  obtain ⟨C, hC⟩ := hφc.isCompact.exists_bound_of_continuousOn hφ.continuousOn
  have hb (z : ℝ) : ‖φ (e.symm z)‖ ≤ max C 0 := by
    by_cases hz : e.symm z ∈ tsupport φ
    · exact (hC _ hz).trans (le_max_left _ _)
    · simp only [image_eq_zero_of_notMem_tsupport hz, norm_zero]
      exact le_max_right _ _
  have hlim := tendsto_gaussianAverage_of_continuous_bounded hf hb (e x)
  simp only [Equiv.symm_apply_apply] at hlim
  refine (tendsto_congr' ?_).2 hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [gaussianAverage_eq_integral_realHeatKernel hf ht]
  have hpush := hp.integral_comp e'.toHomeomorph.measurableEmbedding
    (fun z : ℝ ↦ realHeatKernel t (z - e x) * φ (e.symm z))
  simpa only [Equiv.symm_apply_apply] using hpush

end PoincareConjecture.RiemannianMetric
