import PoincareConjecture.Proofs.M14.Sec6_7_PointwiseMonotonicity
import PoincareConjecture.Proofs.M14.Sec6_7_InitialJacobian
import PoincareConjecture.Proofs.M14.Sec6_7_InitialReducedLength

set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

theorem tendsto_exponentialWeightedJacobian_zero
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (v : Module.Basis (Fin n) ℝ (G.Horizontal x))
    (horth : ∀ i j, G.spacetime.horizontalMetric.inner x (v i) (v j) =
      if i = j then 1 else 0)
    {Z : G.Horizontal x} {b : ℝ} (hb : (Z, b) ∈ E.domain) (hpos : 0 < b) :
    Tendsto (exponentialWeightedJacobian E v Z) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.rpow (2 : ℝ) (n : ℝ) *
        Real.exp (-G.spacetime.horizontalMetric.inner x Z Z))) := by
  have hJ := tendsto_exponentialJacobian_normalized_zero hM04 hM12 E v horth hb hpos
  have hl := tendsto_exponential_reducedLength_zero hM04 hM12 E hb hpos
  have hlim := hJ.mul (Real.continuous_exp.continuousAt.tendsto.comp hl.neg)
  rw [← Real.rpow_natCast (2 : ℝ) n] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change exponentialJacobian E v Z s / s ^ n * Real.exp (-E.reduced_length Z s) =
    s ^ (-(n : ℝ)) * Real.exp (-E.reduced_length Z s) * exponentialJacobian E v Z s
  rw [Real.rpow_neg (le_of_lt hs), Real.rpow_natCast]
  ring

theorem exponentialWeightedJacobian_le_gaussian
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (v : Module.Basis (Fin n) ℝ (G.Horizontal x))
    (horth : ∀ i j, G.spacetime.horizontalMetric.inner x (v i) (v j) =
      if i = j then 1 else 0)
    {τ : ℝ} (H : M14StableSet G T τ x E) {Z : G.Horizontal x} (hZ : Z ∈ H.carrier) :
    exponentialWeightedJacobian E v Z (Real.sqrt τ) ≤
      Real.rpow (2 : ℝ) (n : ℝ) * Real.exp (-G.spacetime.horizontalMetric.inner x Z Z) :=
  positivePrefix_le_initial_limit
    (exponentialWeightedJacobian_antitoneOn hCoordinates hM04 hM12 E v H hZ)
    (tendsto_exponentialWeightedJacobian_zero hM04 hM12 E v horth (H.survivor Z hZ)
      (Real.sqrt_pos.mpr H.tau_pos)) ⟨Real.sqrt_pos.mpr H.tau_pos, le_rfl⟩

theorem stableDensity_mul_jacobian_le_gaussian
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) {τ : ℝ} (H : M14StableSet G T τ x E)
    (D : M14MeasureJacobianData G T τ x E H) {Z : G.Horizontal x} (hZ : Z ∈ H.carrier) :
    stableReducedVolumeDensity H (H.endpoint_slice_map Z) * D.jacobian Z ≤
      Real.rpow (2 : ℝ) (n : ℝ) * Real.exp (-G.spacetime.horizontalMetric.inner x Z Z) := by
  rw [stableDensity_mul_jacobian_eq_weighted E H D hZ]
  exact exponentialWeightedJacobian_le_gaussian hCoordinates hM04 hM12 E D.sourceBasis
    D.source_basis_orthonormal H hZ

end PoincareConjecture.M14
