import PoincareConjecture.Proofs.M30.Thm11_8.ClosedLeftRelatedNecks










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space
  FlowCarrier.measurableSpace FlowCarrier.borelSpace

set_option maxHeartbeats 800000 in

set_option synthInstance.maxHeartbeats 100000 in



theorem exists_generalized_closed_left_related_neck_threshold :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 400 ∧
      ∀ {S : GeneralizedBlowupSequence.{u}} {T : ℝ}, 0 < T →
      ∀ (G : GeneralizedBlowupConvergence S (Ioc (-T) 0))
        (epsilon C : ℝ), 0 < epsilon → epsilon ≤ epsilon0 →
        (∀ k, generalizedEarlierDenseStrongCanonicalNeighborhoods
          (S.flow (G.subsequence k)) epsilon C
          (S.base (G.subsequence k)).1 (S.base (G.subsequence k)).2) →
      ∀ F : RicciFlow 3 G.limit.carrier.carrier (Icc (-T) 0),
        (∀ t ∈ Ioc (-T) 0, F.metric t = G.limit.flow.metric t) →
        MetricComplete (F.metric (-T)) →
      ∀ x : G.limit.carrier.carrier,
        4 < (F.connection (-T)).scalarCurvature x →
        (∃ N : EpsilonNeck (F.metric (-T)),
          N.epsilon = 4 * epsilon ∧ N.connection = F.connection (-T) ∧
          (F.connection (-T)).scalarCurvature x ≤
            16 * max 1 C * (F.connection (-T)).scalarCurvature N.center) ∨
          IsCompact (univ : Set G.limit.carrier.carrier) := by
  classical
  obtain ⟨epsilon0, hpositive, hsmall, hshape⟩ :=
    exists_generalized_canonical_slice_shape_threshold.{u}
  refine ⟨epsilon0, hpositive, hsmall, ?_⟩
  intro S T hT G epsilon C hepsilon hle hdense F hmetric hcomplete x hx
  by_cases hcompact : IsCompact (univ : Set G.limit.carrier.carrier)
  · exact Or.inr hcompact
  apply Or.inl
  apply related_neck_at_left_endpoint_of_interior_necks hT hepsilon
    (hle.trans hsmall) F hcomplete ?_ x hx
  intro t ht y hy
  have hleft : ∃ delta : ℝ, 0 < delta ∧ Icc (t - delta) t ⊆ Ioc (-T) 0 := by
    refine ⟨(t + T) / 2, by linarith [ht.1], ?_⟩
    intro s hs
    exact ⟨by linarith [hs.1, ht.1], hs.2.trans ht.2⟩
  have hreadout
      (g' : RiemannianMetric 3 G.limit.carrier.carrier)
      (heq : g' = G.limit.flow.metric t) (D' : LeviCivitaData g')
      (hy' : 4 < D'.scalarCurvature y) :
      ∃ N : EpsilonNeck g',
        N.epsilon = 2 * epsilon ∧ N.connection = D' ∧
        D'.scalarCurvature y ≤ 4 * max 1 C * D'.scalarCurvature N.center ∧
        N.carrier ⊆ g'.ball y
          (4 * max 1 C + (2 * Real.pi + 2 * (2 * epsilon)⁻¹) * max 1 C + 1) := by
    subst g'
    have hyold : 4 < (G.limit.flow.connection t).scalarCurvature y := by
      simpa only [D'.scalarCurvature_eq (G.limit.flow.connection t)] using hy'
    have hs := (or_assoc.mpr
      (hshape G epsilon C hepsilon hle hdense t ht hleft y hyold)).resolve_right hcompact
    obtain ⟨N, hNepsilon, _hNconnection, hratio, hball⟩ :=
      related_neck_data_of_canonical_slice_shape (G.limit.flow.connection t) hyold hs
    let N' : EpsilonNeck (G.limit.flow.metric t) := {
      N with
      connection := D'
      scalar_center_pos := by
        rw [D'.scalarCurvature_eq N.connection]
        exact N.scalar_center_pos
      scale_eq_scalar := by
        rw [D'.scalarCurvature_eq N.connection]
        exact N.scale_eq_scalar }
    refine ⟨N', hNepsilon, rfl, ?_, hball⟩
    change D'.scalarCurvature y ≤ 4 * max 1 C * D'.scalarCurvature N.center
    simpa only [D'.scalarCurvature_eq (G.limit.flow.connection t)] using hratio
  exact hreadout (F.metric t) (hmetric t ht) (F.connection t) hy

end PoincareConjecture.M30
