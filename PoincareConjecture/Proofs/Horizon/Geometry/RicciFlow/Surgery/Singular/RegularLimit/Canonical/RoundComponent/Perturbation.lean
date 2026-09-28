import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.Jets.Uniform
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.Jets.IntrinsicError
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.RoundComponent.MetricChange



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.SingularTimeAssumptions

open SingularRegularLimit.RoundComparison

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}



theorem eventually_roundComponent_terminal_perturbation
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (hepsilon : H.epsilon ≤ roundComparisonThreshold)
    (x : H.regularRegion P04) (hpos : 0 < (H.terminalConnection P04).scalarCurvature x)
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    (m : ℕ) (hm : m ≤ ⌊H.epsilon⁻¹⌋₊) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ t in 𝓝[<] T,
      ∀ N : SingularRoundComponent ((H.terminalFlow P04).metric t) H.epsilon,
        x ∈ N.carrier → N.carrier ⊆ A → ∀ y : N.model.carrier,
        (∑ j ∈ Finset.range (m + 1),
          (N.model_metric.tensorNorm (N.model_connection.iteratedCovariantTensorDerivative (k := 2)
            (fun z v => (N.normalizedMetricAt (H.terminalMetric P04)).inner z (v 0) (v 1) -
              N.normalizedMetric.inner z (v 0) (v 1)) j) y) ^ 2) ≤ ρ := by
  obtain ⟨s, B, _, hsT, hB, hbound⟩ :=
    H.exists_uniform_round_coordinate_terminal_bound P04 hepsilon x hpos hA m hm
  obtain ⟨C, hC, hintrinsic⟩ := exists_intrinsic_metric_error_bound.{u}
    sphereReferenceMetric.leviCivitaData 0 m
  let u := 2 * (H.terminalConnection P04).scalarCurvature x / 5
  have hu : 0 < u := by dsimp [u]; positivity
  have hlim : Tendsto (fun t : ℝ => C * (u * B * (T - t)) ^ 2) (𝓝[<] T) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => C * (u * B * (T - t)) ^ 2) := by fun_prop
    simpa only [sub_self, mul_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
      (hc.tendsto T).mono_left nhdsWithin_le_nhds
  filter_upwards [Ico_mem_nhdsLT hsT,
    H.eventually_roundComponent_scale_bounds P04 hepsilon x hpos,
    hlim.eventually_lt_const hρ] with t ht hscale hsmall
  intro N hxN hNA y
  obtain ⟨U, f, hU, hzero, hfzero, hf, hinv, hmodel, hjet⟩ := hbound t ht N hxN hNA y
  have hscale' : N.scale ≤ u := (hscale N hxN).2.le
  have hdelta : 0 ≤ T - t := sub_nonneg.mpr ht.2.le
  have hjets : ∀ j ≤ m,
      ‖iteratedFDeriv ℝ j
        ((N.normalizedMetricAt (H.terminalMetric P04)).pullbackCoefficients f -
          (N.normalizedMetricAt ((H.terminalFlow P04).metric t)).pullbackCoefficients f) 0‖ ≤
        u * B * (T - t) := by
    intro j hj
    rw [N.normalizedMetricAt_pullback_difference_jet_eq _ _ hU hf hzero j,
      norm_smul, Real.norm_eq_abs, abs_of_pos N.scale_pos]
    calc
      _ ≤ N.scale * (B * (T - t)) := mul_le_mul_of_nonneg_left (hjet j hj) N.scale_pos.le
      _ ≤ u * (B * (T - t)) := mul_le_mul_of_nonneg_right hscale' (mul_nonneg hB hdelta)
      _ = u * B * (T - t) := by ring
  have h := hintrinsic N.model_connection hU hzero hf hinv hmodel
    (u * B * (T - t)) (by positivity) hjets
  have h' := h.trans hsmall.le
  simpa only [hfzero, SingularRoundComponent.normalizedMetricAt_self] using h'

end PoincareConjecture.SingularTimeAssumptions
