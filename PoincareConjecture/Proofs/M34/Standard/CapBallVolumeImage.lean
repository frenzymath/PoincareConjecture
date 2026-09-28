import PoincareConjecture.Proofs.M34.Standard.CapIntrinsicDiameter
import PoincareConjecture.Proofs.M34.Standard.LocalCalibratedImageVolume











set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric




theorem image_ball_subset_ball_of_tangentNorm_le_on_open
    {n m : ℕ} {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) X]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 m) ∞ X]
    (g : RiemannianMetric n M) (h : RiemannianMetric m X)
    (f : M → X) {U : Set M} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 m) 1 f U)
    {K : ℝ} (hK : 0 < K)
    (hbound : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 n) x,
      h.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 m) f x v) ≤ K * g.tangentNorm x v)
    {y : M} {r R : ℝ} (hsource : g.ball y r ⊆ U) (hrR : K * r ≤ R) :
    f '' g.ball y r ⊆ h.ball (f y) R := by
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨γ, hγ0, hγ1, hγ, hlen, hball⟩ := g.exists_short_path_in_ball y z hz
  have hγU : MapsTo γ (Icc (0 : ℝ) 1) U := fun t ht => hsource (hball ht)
  have hη : ContMDiffOn 𝓘(ℝ) (𝓡 m) 1 (f ∘ γ) (Icc (0 : ℝ) 1) :=
    hf.comp hγ hγU
  have hlength := g.pathELength_comp_le_of_pointwise_tangentNorm_le h f
    (fun x hx => (hf x hx).contMDiffAt (hU.mem_nhds hx)) hK.le hbound
    γ 0 1 hγ hγU
  have hdist : h.edist (f y) (f z) ≤ h.pathELength (f ∘ γ) 0 1 := by
    simpa only [Function.comp_apply, hγ0, hγ1] using
      h.edist_le_pathELength_of_mem_Icc hη (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
  have hstrict := ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hK).ne'
    ENNReal.ofReal_ne_top hlen
  rw [← ENNReal.ofReal_mul hK.le] at hstrict
  exact ((hdist.trans hlength).trans_lt hstrict).trans_le (ENNReal.ofReal_le_ofReal hrR)

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.M34

variable {n : ℕ} {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ X]
  [MeasurableSpace M] [MeasurableSpace X] [BorelSpace M] [BorelSpace X]
  [T3Space M] [T3Space X] [SecondCountableTopology X]




theorem calibrated_ball_volume_le_mul_of_image_subset
    (g : RiemannianMetric n M) (h : RiemannianMetric n X)
    (e : OpenPartialHomeomorph M X)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    (hi : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    {K : ℝ} (hK : 0 < K)
    (hbound : ∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 n) x,
      g.tangentNorm x v ≤ K * h.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v))
    {y : M} {r R : ℝ} (hsource : g.ball y r ⊆ e.source)
    (himage : e '' g.ball y r ⊆ h.ball (e y) R) :
    calibratedMetricVolume g (g.ball y r) ≤
      ENNReal.ofReal K ^ n * calibratedMetricVolume h (h.ball (e y) R) := by
  let : EMetricSpace M := g.comparisonEMetric
  have hopen : IsOpen (g.ball y r) :=
    isOpen_lt (continuous_const.edist continuous_id) continuous_const
  have hvol := calibratedMetricVolume_le_mul_image_of_local_tangentNorm_lower
    g h e hf hi hK hbound hopen.measurableSet hsource
  exact hvol.trans (mul_le_mul_right (measure_mono himage) (ENNReal.ofReal K ^ n))




theorem calibrated_ball_volume_le_mul_of_tangent_bounds
    (g : RiemannianMetric n M) (h : RiemannianMetric n X)
    (e : OpenPartialHomeomorph M X)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    (hi : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    {K L : ℝ} (hK : 0 < K) (hL : 0 < L)
    (hupper : ∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 n) x,
      h.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) ≤ K * g.tangentNorm x v)
    (hlower : ∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 n) x,
      g.tangentNorm x v ≤ L * h.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v))
    {y : M} {r R : ℝ} (hsource : g.ball y r ⊆ e.source) (hrR : K * r ≤ R) :
    calibratedMetricVolume g (g.ball y r) ≤
      ENNReal.ofReal L ^ n * calibratedMetricVolume h (h.ball (e y) R) :=
  calibrated_ball_volume_le_mul_of_image_subset g h e hf hi hL hlower hsource
    (g.image_ball_subset_ball_of_tangentNorm_le_on_open h e e.open_source hf hK hupper hsource hrR)

end PoincareConjecture.M34
