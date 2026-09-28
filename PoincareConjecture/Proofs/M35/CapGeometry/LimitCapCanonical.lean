import PoincareConjecture.Proofs.M35.CapGeometry.ActualCapTransfer
import PoincareConjecture.Proofs.M35.CapGeometry.CertificateConnection
import PoincareConjecture.Proofs.M35.CapGeometry.SliceCapCertificate
import PoincareConjecture.Proofs.M35.Thm12_28.CapCompactness









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

local notation "E3" => EuclideanSpace ℝ (Fin 3)



theorem blowupSequence_limit_cap_canonical (P : M35StandardCapPredecessors) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ {g₀ : StandardInitialMetric}
      (E : RepairedStandardCapExistenceData g₀)
      (NC : StandardFlowNoncollapsingCertificate E.flow)
      (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
      (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
      (_htone : Tendsto t atTop (𝓝 1))
      (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
      (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
        (blowupBackwardInterval ⊤)) (kappa : ℝ)
      (A : BlowupAncientKappaIdentification L.limit kappa),
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
    letI : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
    letI : ChartedSpace E3 L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    letI : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
    letI : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
    letI : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
    letI : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
    ∀ (epsilon C : ℝ) (N : M27CanonicalCap A.solution 0 L.limit.base epsilon C),
      epsilon ≤ delta → ∀ j : ℕ, closure N.cap.carrier ⊆ L.exhaustion.space j →
      ∀ᶠ k in atTop, GeneralizedCanonicalControl
        (F := generalizedFlow E.flow.base.flow) (t (L.subsequence k))
        ((sliceDiffeomorph (ht (L.subsequence k))).symm (x (L.subsequence k)))
        epsilon (8 * C + 16 / NC.kappa) := by
  obtain ⟨delta, hdelta, htransfer⟩ := blowupSequence_cap_certificate P
  refine ⟨delta, hdelta, ?_⟩
  intro g₀ E NC t x ht htone hR L kappa A
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace E3 L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  intro epsilon C N he j hstage
  obtain ⟨N', hepsilon, hconstant, hconnection, hcarrier, hcore, _⟩ :=
    N.cap.exists_of_metric_eq (A.metric_eq 0 le_rfl) (L.limit.flow.connection 0)
  have hc : IsCompact (closure N'.carrier) := by
    rw [hcarrier]
    exact N.cap.isCompact_closure (A.solution.complete 0 le_rfl)
  have hstage' : closure N'.carrier ⊆ L.exhaustion.space j := by
    rwa [hcarrier]
  have hreturned := htransfer E NC t x ht htone hR L j N'
    (by rw [hepsilon, N.epsilon_eq]; exact he) hconnection hc hstage'
  filter_upwards [hreturned] with k hk
  obtain ⟨K, hKe, hKC, hKD, _hKU, hKcore, _⟩ := hk
  have hbase : ((L.embedding k).forward 0
      ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ L.limit.base).val =
        x (L.subsequence k) := by
    exact congrArg (fun p : (generalizedFlow E.flow.base.flow).point => p.2.val)
      (L.base_preserving k _)
  have hx : x (L.subsequence k) ∈ K.core := by
    rw [hKcore]
    exact ⟨L.limit.base, hcore.symm ▸ N.contains, hbase⟩
  apply K.generalized_canonical_control P E.flow (ht (L.subsequence k))
    (hKe.trans (hepsilon.trans N.epsilon_eq)) _ hKD hx
  rw [hKC, hconstant]
  linarith [N.constant_le]

end PoincareConjecture.M35.OrdinaryRealization
