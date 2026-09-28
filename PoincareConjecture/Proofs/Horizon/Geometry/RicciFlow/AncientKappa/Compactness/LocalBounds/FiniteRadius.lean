import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.LocalBounds.AuxiliaryContradiction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance finiteRadiusCarrierConnected (C : FlowCarrier.{0} 3) : ConnectedSpace C.carrier :=
  connectedSpace_iff_univ.mpr C.connected

theorem m23_exists_curvature_bound_of_volume_lower_bound
    (P : M23NormalizedKappaCompactnessPredecessors)
    {κ ν : ℝ} (hκ : 0 < κ) (hν : 0 < ν) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (C : FlowCarrier.{0} 3) (K : AncientKappaSolution 3 C.carrier),
      K.kappa = κ → ∀ (p x : C.carrier) (r : ℝ), 0 < r →
      x ∈ (K.flow.metric 0).ball p r →
      ENNReal.ofReal (ν * r ^ 3) ≤ calibratedMetricVolume (K.flow.metric 0)
        ((K.flow.metric 0).ball p r) →
      r ^ 2 * (K.flow.connection 0).scalarCurvature x ≤ A := by
  classical
  by_contra hn
  have hbad (A : ℝ) (hA : 0 ≤ A) :
      ∃ (C : FlowCarrier.{0} 3) (K : AncientKappaSolution 3 C.carrier), K.kappa = κ ∧
        ∃ (p x : C.carrier) (r : ℝ), 0 < r ∧ x ∈ (K.flow.metric 0).ball p r ∧
          ENNReal.ofReal (ν * r ^ 3) ≤ calibratedMetricVolume (K.flow.metric 0)
            ((K.flow.metric 0).ball p r) ∧
          A < r ^ 2 * (K.flow.connection 0).scalarCurvature x := by
    by_contra hbad
    apply hn
    refine ⟨A, hA, ?_⟩
    intro C K hkappa p x r hr hx hvolume
    by_contra hbound
    exact hbad ⟨C, K, hkappa, p, x, r, hr, hx, hvolume, lt_of_not_ge hbound⟩
  choose C K hkappa p x r hr hx hvolume hscale using
    fun k : ℕ ↦ hbad (k : ℝ) (Nat.cast_nonneg k)
  obtain ⟨S, _, _, hbound, hvolume⟩ :=
    m23_exists_controlled_sequence_of_unbounded_curvature_scale P C K hκ hν.le
      hkappa p x r hr hx hvolume
      (tendsto_atTop_mono (fun k ↦ (hscale k).le) tendsto_natCast_atTop_atTop)
  exact S.false_of_eventually_bounded_curvature_and_positive_volume_ratio
    P (by norm_num) (div_pos hν (by norm_num)) hbound hvolume

end PoincareConjecture
