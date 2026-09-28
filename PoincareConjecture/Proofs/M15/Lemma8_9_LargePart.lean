import PoincareConjecture.Proofs.M15.Prop8_2_ImageRestriction
import PoincareConjecture.Proofs.M15.Mathlib.GaussianTail
import PoincareConjecture.Proofs.M15.Mathlib.OrthonormalGaussian










set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.Proofs.M15

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}
  {H : M14StableSet G T τ x E}



theorem horizontal_gaussian_integral
    (A : M14ReducedVolumeAnalyticData G T τ x E H) {c : ℝ} (hc : 0 < c) :
    (∫ Z, Real.exp (-c * G.spacetime.horizontalMetric.inner x Z Z)
      ∂A.measure_data.sourceMeasure) = Real.rpow (Real.pi / c) ((n : ℝ) / 2) := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  have : FiniteDimensional ℝ (G.Horizontal x) :=
    A.measure_data.sourceBasis.finiteDimensional_of_finite
  rw [A.measure_data.source_volume_eq_metric_volume]
  exact integral_exp_neg_bilin_of_orthonormal_basis (n := n) (E := G.Horizontal x)
    A.measure_data.sourceBasis
    (G.spacetime.horizontalMetric.inner x) A.measure_data.source_basis_orthonormal hc



theorem horizontal_gaussian_integrable
    (A : M14ReducedVolumeAnalyticData G T τ x E H) {c : ℝ} (hc : 0 < c) :
    Integrable (fun Z => Real.exp (-c * G.spacetime.horizontalMetric.inner x Z Z))
      A.measure_data.sourceMeasure := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  have : FiniteDimensional ℝ (G.Horizontal x) :=
    A.measure_data.sourceBasis.finiteDimensional_of_finite
  rw [A.measure_data.source_volume_eq_metric_volume]
  exact integrable_exp_neg_bilin_of_orthonormal_basis (n := n) (E := G.Horizontal x)
    A.measure_data.sourceBasis
    (G.spacetime.horizontalMetric.inner x) A.measure_data.source_basis_orthonormal hc



theorem reducedVolumeOn_large_part_le
    (S : M14ReducedVolumeSourceCoverageData G)
    (A : M14ReducedVolumeAnalyticData G T τ x E H)
    {W : Set (G.Horizontal x)} (hW : MeasurableSet W) (hWH : W ⊆ H.carrier)
    {a : ℝ} (ha : ∀ Z ∈ W, a ≤ G.spacetime.horizontalMetric.inner x Z Z) :
    M14ReducedVolumeOnAnalyticCarrier A W ≤
      (Real.rpow 2 (n : ℝ) * Real.rpow (2 * Real.pi) ((n : ℝ) / 2)) *
        Real.exp (-a / 2) := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  have hhalf_eq : (fun Z => Real.exp (-G.spacetime.horizontalMetric.inner x Z Z / 2)) =
      (fun Z => Real.exp (-(1 / 2 : ℝ) * G.spacetime.horizontalMetric.inner x Z Z)) := by
    funext Z
    congr 1
    ring
  have hhalf : Integrable
      (fun Z => Real.exp (-G.spacetime.horizontalMetric.inner x Z Z / 2))
      A.measure_data.sourceMeasure := by
    rw [hhalf_eq]
    exact horizontal_gaussian_integrable A (by norm_num)
  have heval : (∫ Z, Real.exp (-G.spacetime.horizontalMetric.inner x Z Z / 2)
      ∂A.measure_data.sourceMeasure) =
      Real.rpow (2 * Real.pi) ((n : ℝ) / 2) := by
    rw [hhalf_eq, horizontal_gaussian_integral A (by norm_num)]
    congr 1
    ring
  have henergy : Measurable (fun Z => G.spacetime.horizontalMetric.inner x Z Z) := by
    have hcont : Continuous (fun Z => G.spacetime.horizontalMetric.inner x Z Z) := by
      fun_prop
    exact hcont.measurable
  have htail := setIntegral_exp_neg_le_half henergy hW hhalf ha
  rw [heval] at htail
  have hgaussian : Integrable
      (fun Z => Real.exp (-G.spacetime.horizontalMetric.inner x Z Z))
      A.measure_data.sourceMeasure := by
    simpa only [neg_one_mul] using horizontal_gaussian_integrable A (c := 1) zero_lt_one
  have hinitial_eq : A.initial_density =
      (fun Z => Real.rpow 2 (n : ℝ) *
        Real.exp (-G.spacetime.horizontalMetric.inner x Z Z)) :=
    funext A.initial_density_eq
  have hinitial : Integrable A.initial_density A.measure_data.sourceMeasure := by
    rw [hinitial_eq]
    exact hgaussian.const_mul _
  calc
    M14ReducedVolumeOnAnalyticCarrier A W ≤
        ∫ Z in W, A.initial_density Z ∂A.measure_data.sourceMeasure :=
      reducedVolumeOn_le_initial_density S A hW hWH hinitial.integrableOn
    _ = Real.rpow 2 (n : ℝ) *
        ∫ Z in W, Real.exp (-G.spacetime.horizontalMetric.inner x Z Z)
          ∂A.measure_data.sourceMeasure := by
      rw [hinitial_eq, integral_const_mul]
    _ ≤ Real.rpow 2 (n : ℝ) *
        (Real.exp (-a / 2) * Real.rpow (2 * Real.pi) ((n : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left htail.2 (Real.rpow_nonneg (by norm_num) _)
    _ = _ := by ring





theorem exists_large_vector_threshold (n : ℕ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ {X : Type u} [TopologicalSpace X] {time : X → ℝ} {I : SpacetimeInterval}
        {G : GeneralizedLGeometryTransport n X time I}
        {T τ : ℝ} {x : G.Point} {E : M14ExponentialFamily G T x}
        {H : M14StableSet G T τ x E}
        (_S : M14ReducedVolumeSourceCoverageData G)
        (A : M14ReducedVolumeAnalyticData G T τ x E H)
        {W : Set (G.Horizontal x)},
        MeasurableSet W → W ⊆ H.carrier →
        (∀ Z ∈ W, 1 / (64 * ε) ≤ G.spacetime.horizontalMetric.inner x Z Z) →
        M14ReducedVolumeOnAnalyticCarrier A W ≤ Real.rpow ε ((n : ℝ) / 2) := by
  obtain ⟨ε₀, hε₀, hsmall⟩ := Real.exists_pos_exp_neg_div_le_rpow
    (Real.rpow 2 (n : ℝ) * Real.rpow (2 * Real.pi) ((n : ℝ) / 2))
    ((n : ℝ) / 2) (b := (1 / 128 : ℝ)) (by norm_num)
  refine ⟨ε₀, hε₀, ?_⟩
  intro ε hε hε₀' X instX time I G T τ x E H S A W hW hWH ha
  have htail := reducedVolumeOn_large_part_le S A hW hWH ha
  have hexponent : -(1 / (64 * ε)) / 2 = -(1 / 128 : ℝ) / ε := by
    field_simp
    ring
  rw [hexponent] at htail
  exact htail.trans (hsmall ε hε hε₀')

end PoincareConjecture.Proofs.M15
