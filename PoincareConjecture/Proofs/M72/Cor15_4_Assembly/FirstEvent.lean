import PoincareConjecture.Proofs.M72.Cor15_4_Assembly.HistoryIndices

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
  [SecondCountableTopology M]
  {N : NormalizedInitialMetric (M := M)}

theorem m72LedgerNonempty (I : M72ReconstructionInput N)
    (L : M72ReconstructionLedger I) : L.event_times.Nonempty := by
  refine ⟨I.extinction.extinction_time, ?_⟩
  change I.extinction.extinction_time ∈ (↑L.event_times : Set ℝ)
  rw [L.event_times_eq]
  exact ⟨I.extinction.extinction_surgery_mem,
    I.global.certificate.flow.time_domain_nonnegative I.extinction.extinction_mem, le_rfl⟩

theorem m72FirstEventExists (I : M72ReconstructionInput N)
    (L : M72ReconstructionLedger I) :
    ∃ e : M72EventIndex I L, ∀ e' : M72EventIndex I L, e.1 ≤ e'.1 := by
  let hnonempty := m72LedgerNonempty I L
  refine ⟨⟨L.event_times.min' hnonempty, L.event_times.min'_mem hnonempty⟩, ?_⟩
  intro e'
  exact L.event_times.min'_le e'.1 e'.2

noncomputable def m72FirstReferenceToInitial (I : M72ReconstructionInput N)
    (L : M72ReconstructionLedger I) (e : M72EventIndex I L)
    (hfirst : ∀ e' : M72EventIndex I L, e.1 ≤ e'.1) :
    Diffeomorph (𝓡 3) (𝓡 3)
      (I.global.certificate.flow.slice (M72EventTopology I L e).pre_time).carrier
      (I.global.certificate.flow.slice 0).carrier ∞ := by
  have hpred := m72FirstEventPredecessor I L e hfirst
  rw [← hpred]
  exact (M72EventTopology I L e).predecessor_transport.symm

noncomputable def m72FirstEventAssembly (I : M72ReconstructionInput N)
    (L : M72ReconstructionLedger I) (e : M72EventIndex I L)
    (hfirst : ∀ e' : M72EventIndex I L, e.1 ≤ e'.1)
    (R : M72IndexedAssembly (m72TailSummandPiece I L e)
      (I.global.certificate.flow.slice (M72EventTopology I L e).pre_time)) :
    M72IndexedAssembly (m72SummandPiece I L) (I.global.certificate.flow.slice 0) :=
  (R.reindex (m72FirstTailEquiv I L e hfirst)
    (m72FirstTailEquiv_piece I L e hfirst)).transportTarget
      (m72FirstReferenceToInitial I L e hfirst)

theorem m72InitialSliceConnected (I : M72ReconstructionInput N) :
    IsConnected (Set.univ : Set (I.global.certificate.flow.slice 0).carrier) := by
  have himage := I.initial_connected.image I.global.certificate.initial_identification
    I.global.certificate.initial_identification.continuous.continuousOn
  rw [Set.image_univ] at himage
  have hrange : Set.range (I.global.certificate.initial_identification : M → _) = Set.univ :=
    I.global.certificate.initial_identification.surjective.range_eq
  rwa [hrange] at himage

end PoincareConjecture
