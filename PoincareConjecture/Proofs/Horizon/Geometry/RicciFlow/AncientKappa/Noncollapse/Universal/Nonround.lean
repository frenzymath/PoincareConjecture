import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Convergence.Alternative
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Convergence.Region
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.ReducedLength.Region
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Estimate
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Rescaling.Sequence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.TimeShift
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.ClosedCylinders

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u
namespace PoincareConjecture.M22UniversalNoncollapsingPredecessors

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

variable {d : ℕ} (H : M22UniversalNoncollapsingPredecessors.{u} d)
  {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem nonround_volume_lower_bound_zero (K : AncientKappaSolution 3 M)
    (hnonround : ¬ IsRoundAncientKappaSolution K) (p : M) (r : ℝ) (hr : 0 < r)
    (hcurv : ∀ s ∈ Icc (0 - r ^ 2) 0, ∀ x ∈ (K.flow.metric 0).ball p r,
      |(K.flow.connection s).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal ((universalNoncollapseData H.noncollapse_generalized).universal_kappa * r ^ 3) ≤
      calibratedMetricVolume (K.flow.metric 0) ((K.flow.metric 0).ball p r) := by
  classical
  let τ : ℕ → ℝ := fun k ↦ (k : ℝ) + 1
  have hτ : ∀ k, 0 < τ k := fun k ↦ by dsimp [τ]; positivity
  have hτlim : Tendsto τ atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  obtain ⟨B⟩ := H.blowup_setup.setup M K p τ hτ hτlim
  let S := B.sequence
  have hreference : S.reference = p := B.reference_eq
  obtain ⟨L, hmodelVolume, hmodelScalar⟩ := H.exists_normalized_nonround_limit K hnonround S
  let G := L.convergence
  have hvolume := G.eventually_model_region_volume_lower
    (fun t _ ↦ H.tensor_calculus 3 M _ _) hmodelVolume
  have hscalar := G.eventually_model_scalar_lt (fun x ↦ by rw [hmodelScalar]; norm_num)
  have hradius := S.normalized_radius_sq_eventually_le_two G.subsequence_strictMono r
  obtain ⟨k, hkvolume, hkscalar, hkradius⟩ := (hvolume.and (hscalar.and hradius)).exists
  let i := G.subsequence k
  let R := S.rescaling i
  obtain ⟨W⟩ := H.ordinary_rescaling 3 M closedAncientInterval K.flow
    (S.scale i)⁻¹ (inv_pos.mpr R.tau_pos) 0
  let A := R.closedExtension W
  let ρ := Real.sqrt (S.scale i)⁻¹ * r
  have hρ : 0 < ρ := mul_pos (Real.sqrt_pos.mpr (inv_pos.mpr (S.scale_pos i))) hr
  have hρtime : ρ ^ 2 ≤ 2 := hkradius
  have hcurvA : ∀ s ∈ Icc (0 - ρ ^ 2) 0, ∀ x ∈ (A.flow.metric 0).ball p ρ,
      (A.flow.connection s).curvatureTensorNorm x ≤ ρ⁻¹ ^ 2 := by
    intro s hs x hx
    apply (le_abs_self _).trans
    exact R.closedExtension_closed_curvature_bound W p r
      (by simpa only [zero_sub] using hcurv) s (by simpa only [zero_sub] using hs) x hx
  let U := (A.flow.metric (-1)).ball (S.base i) (1 / 2)
  have hU : IsOpen U := (ordinaryMetricBallSource (A.flow.metric (-1)) (S.base i) (1 / 2)).isOpen
  have hUvolume : ENNReal.ofReal universalNoncollapseVolume ≤
      calibratedMetricVolume (A.flow.metric (-2)) U := by
    change ENNReal.ofReal universalNoncollapseVolume ≤
      calibratedMetricVolume ((R.closedExtension W).flow.metric (-2))
        (((R.closedExtension W).flow.metric (-1)).ball (S.base i) (1 / 2))
    rw [calibratedMetricVolume_eq_volumeMeasure,
      R.closedExtension_metric_eq W (-2) (by norm_num),
      R.closedExtension_metric_eq W (-1) (by norm_num)]
    exact hkvolume (-2) (by norm_num)
  have hseed : reducedLength A.flow 0 p (S.base i) 1 ≤ 3 := by
    have h := S.closedExtension_base_reduced_length_bound i W
    rw [hreference] at h
    exact h.trans (by norm_num)
  have hAscalar : ∀ x ∈ (A.flow.metric (-1)).ball (S.base i) 1,
      (A.flow.connection (-1)).scalarCurvature x ≤ 2 := by
    intro x hx
    change x ∈ ((R.closedExtension W).flow.metric (-1)).ball (S.base i) 1 at hx
    rw [R.closedExtension_metric_eq W (-1) (by norm_num)] at hx
    change ((R.closedExtension W).flow.connection (-1)).scalarCurvature x ≤ 2
    rw [R.closedExtension_scalar W (-1) (by norm_num)]
    exact (hkscalar x hx).le
  have hlength : ∀ q ∈ U, reducedLength A.flow 0 p q 2 ≤ universalNoncollapseLength :=
    H.reducedLength_two_le_on_ball A p (S.base i) hseed hAscalar
  have hbound := H.volume_lower_bound_of_terminal_region A p ρ hρ hρtime hcurvA
    U hU hUvolume hlength
  exact (R.closedExtension_ball_volume_lower_bound_iff W p r
    (universalNoncollapseData H.noncollapse_generalized).universal_kappa).mp hbound

theorem nonround_is_universally_noncollapsed (K : AncientKappaSolution 3 M)
    (hnonround : ¬ IsRoundAncientKappaSolution K) :
    AncientKappaNoncollapsed K.flow
      (universalNoncollapseData H.noncollapse_generalized).universal_kappa := by
  apply ancientKappaNoncollapsed_of_closed_cylinders
  intro t ht p r hr hcurv
  obtain ⟨W⟩ := H.ordinary_rescaling 3 M closedAncientInterval K.flow 1 zero_lt_one t
  let A := K.closedTimeShift t ht W
  have hAnonround : ¬ IsRoundAncientKappaSolution A := fun hround ↦
    hnonround (AncientKappaRoundness.isRoundAncientKappaSolution_of_closedTimeShift
      H K t ht W hround)
  have hcurvA : ∀ s ∈ Icc (0 - r ^ 2) 0, ∀ x ∈ (A.flow.metric 0).ball p r,
      |(A.flow.connection s).curvatureTensorNorm x| ≤ r⁻¹ ^ 2 := by
    intro s hs x hx
    change x ∈ ((K.closedTimeShift t ht W).flow.metric 0).ball p r at hx
    rw [K.closedTimeShift_metric t ht W, zero_add] at hx
    change |((K.closedTimeShift t ht W).flow.connection s).curvatureTensorNorm x| ≤ _
    rw [K.closedTimeShift_curvature_norm]
    exact hcurv (s + t) ⟨by linarith [hs.1], by linarith [hs.2]⟩ x hx
  have hbound := H.nonround_volume_lower_bound_zero A hAnonround p r hr hcurvA
  simpa only [A, K.closedTimeShift_metric, zero_add] using hbound

end PoincareConjecture.M22UniversalNoncollapsingPredecessors
