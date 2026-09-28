import PoincareConjecture.Proofs.M49.VolumeDensity
import PoincareConjecture.Proofs.M49.Mathlib.ExponentialComparison
import PoincareConjecture.Proofs.M10.CalibratedTransport

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M49

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J)

theorem pullbackJacobian_le_exp_mul
    (f : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n))
    (hD : Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x))
    {a b k : ℝ} (hab : a ≤ b) (hJ : Icc a b ⊆ J)
    (hscalar : ∀ t ∈ Icc a b, -k ≤ (F.connection t).scalarCurvature (f x)) :
    M10.pullbackJacobian (F.metric b) f x ≤
      Real.exp (k * (b - a)) * M10.pullbackJacobian (F.metric a) f x := by
  apply Real.le_exp_mul_of_hasDerivAt_le hab
    ((pullbackJacobian_continuousOn_time F f x).mono hJ)
    (f' := fun t => -(F.connection t).scalarCurvature (f x) *
      M10.pullbackJacobian (F.metric t) f x)
  · intro t ht
    exact pullbackJacobian_hasDerivAt F f x hD
      (mem_of_superset (isOpen_Ioo.mem_nhds ht) (Ioo_subset_Icc_self.trans hJ))
  · intro t ht
    apply mul_le_mul_of_nonneg_right _ (M10.pullbackJacobian_nonneg _ _ _)
    linarith [hscalar t ⟨ht.1.le, ht.2.le⟩]

variable [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem calibratedMetricVolume_image_le_exp_mul
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    {a b k : ℝ} (hab : a ≤ b) (hJ : Icc a b ⊆ J)
    (hscalar : ∀ t ∈ Icc a b, ∀ x : M, -k ≤ (F.connection t).scalarCurvature x)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A) (hAs : A ⊆ e.source) :
    calibratedMetricVolume (F.metric b) (e '' A) ≤
      ENNReal.ofReal (Real.exp (k * (b - a))) *
        calibratedMetricVolume (F.metric a) (e '' A) := by
  have heD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn one_ne_zero, hei.mdifferentiableOn one_ne_zero⟩
  rw [M10.calibratedMetricVolume_image_eq_lintegral (F.metric b) e he hei hA hAs,
    M10.calibratedMetricVolume_image_eq_lintegral (F.metric a) e he hei hA hAs]
  calc
    _ ≤ ∫⁻ x in A, ENNReal.ofReal (Real.exp (k * (b - a))) *
        ENNReal.ofReal (M10.pullbackJacobian (F.metric a) e x) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hA] with x hx
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      exact ENNReal.ofReal_le_ofReal (pullbackJacobian_le_exp_mul F e x
        (heD.mfderiv_bijective (hAs hx)) hab hJ (fun t ht => hscalar t ht (e x)))
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

variable [SecondCountableTopology M]

theorem calibratedMetricVolume_le_exp_mul
    {a b k : ℝ} (hab : a ≤ b) (hJ : Icc a b ⊆ J)
    (hscalar : ∀ t ∈ Icc a b, ∀ x : M, -k ≤ (F.connection t).scalarCurvature x)
    {A : Set M} (hA : MeasurableSet A) :
    calibratedMetricVolume (F.metric b) A ≤
      ENNReal.ofReal (Real.exp (k * (b - a))) * calibratedMetricVolume (F.metric a) A := by
  apply M10.measure_le_mul_of_local_comparison (U := univ) _ hA (subset_univ A)
  intro p _
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
  refine ⟨e.target, e.open_target, mem_chart_source _ _, ?_⟩
  intro B hB hBe
  have hpre : MeasurableSet ((Subtype.val : e.source → EuclideanSpace ℝ (Fin n)) ⁻¹'
      (e ⁻¹' B)) := hB.preimage e.continuousOn.domRestrict.measurable
  have hC : MeasurableSet (e ⁻¹' B ∩ e.source) := by
    simpa only [Subtype.range_coe] using
      (MeasurableEmbedding.subtype_coe e.open_source.measurableSet).measurableSet_preimage.mp
        hpre
  have h := calibratedMetricVolume_image_le_exp_mul F e contMDiffOn_chart_symm
    contMDiffOn_chart hab hJ hscalar hC inter_subset_right
  rw [image_preimage_inter, e.image_source_eq_target, inter_eq_left.mpr hBe] at h
  exact h

end PoincareConjecture.M49
