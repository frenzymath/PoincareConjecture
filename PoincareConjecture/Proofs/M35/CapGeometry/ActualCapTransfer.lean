import PoincareConjecture.Proofs.M35.CapGeometry.SelectedCertificate
import PoincareConjecture.Proofs.M35.CapGeometry.SelectedFullStaticNeck










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization




theorem blowupSequence_cap_certificate
    (P : M35StandardCapPredecessors) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ {g₀ : StandardInitialMetric}
      (E : RepairedStandardCapExistenceData g₀)
      (NC : StandardFlowNoncollapsingCertificate E.flow)
      (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
      (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
      (_htone : Tendsto t atTop (𝓝 1))
      (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
      (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
        (blowupBackwardInterval ⊤)) (j : ℕ),
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
    letI : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    letI : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
    letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
    letI : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
    ∀ N : CapCertificate (L.limit.flow.metric 0), N.epsilon ≤ delta →
      N.connection = L.limit.flow.connection 0 →
      IsCompact (closure N.carrier) → closure N.carrier ⊆ L.exhaustion.space j →
      ∀ᶠ k in atTop,
        let f : L.limit.carrier.carrier → StandardCapSpace := fun z =>
          ((L.embedding k).forward 0
            ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
        ∃ C : CapCertificate (E.flow.metric (t (L.subsequence k))),
          C.epsilon = N.epsilon ∧
          C.cap_constant = 8 * N.cap_constant + 16 / NC.kappa ∧
          C.connection = E.flow.connection (t (L.subsequence k)) ∧
          C.carrier = f '' N.carrier ∧ C.core = f '' N.core ∧
          C.closed_core = f '' N.closed_core ∧ C.boundary_sphere = f '' N.boundary_sphere ∧
          C.model_kind = N.model_kind := by
  obtain ⟨delta, hdelta, htransfer⟩ :=
    blowupSequence_cap_certificate_of_full_neck_comparisons P
  refine ⟨delta, hdelta, ?_⟩
  intro g₀ E NC t x ht htone hR L j
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  intro N hfine hconnection hcompact hstage
  have he : N.epsilon ≤ 1 / 24 := N.epsilon_le_threshold.trans (by norm_num)
  have hend := blowupSequence_full_static_neck_close P E t x ht hR L N.end_neck
    (N.end_neck_epsilon.symm ▸ he) (N.end_neck_connection.trans hconnection)
    (hcompact.of_isClosed_subset isClosed_closure (closure_mono N.end_neck_subset)) j
    ((closure_mono N.end_neck_subset).trans hstage)
  have hboundary := blowupSequence_full_static_neck_close P E t x ht hR L N.boundary_neck
    (N.boundary_neck_epsilon.symm ▸ he) (N.boundary_neck_connection.trans hconnection)
    (hcompact.of_isClosed_subset isClosed_closure (closure_mono N.boundary_neck_subset)) j
    ((closure_mono N.boundary_neck_subset).trans hstage)
  apply htransfer E NC t x ht htone hR L j N hfine hconnection hcompact hstage
  filter_upwards [hend, hboundary] with k hkE hkB
  exact ⟨N.end_neck_epsilon ▸ hkE, N.boundary_neck_epsilon ▸ hkB⟩

end PoincareConjecture.M35.OrdinaryRealization
