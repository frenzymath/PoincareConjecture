import PoincareConjecture.Proofs.M72.Cor15_4_Assembly.FirstEvent
import PoincareConjecture.Proofs.M72.Cor15_4_Assembly.ReverseInduction

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
  [SecondCountableTopology M]
  {N : NormalizedInitialMetric (M := M)}

noncomputable def m72ReconstructionConclusion (I : M72ReconstructionInput N) :
    M72ReconstructionConclusion I := by
  let L := m72ReconstructionLedger I
  let hfirstExists := m72FirstEventExists I L
  let e := Classical.choose hfirstExists
  have hfirst : ∀ e' : M72EventIndex I L, e.1 ≤ e'.1 :=
    Classical.choose_spec hfirstExists
  let Rtail := Classical.choice (m72ReverseInduction I L e)
  let R := m72FirstEventAssembly I L e hfirst Rtail
  exact
    { ledger := L
      summand_count := R.count
      summand_index := R.index
      summand_index_bijective := R.index.bijective
      pieces := fun j => m72SummandPiece I L (R.index j)
      piece_eq := fun _ => rfl
      piece_kind := fun j => (R.index j).2.2
      survivor_transport := m72SuccessorChoice I L
      survivor_target_in_ledger := fun e' i hi =>
        m72SuccessorTargetInLedger I L e' i (m72SuccessorChoice I L e' i hi)
      assembly := R.assembly
      target_nonempty := I.global.certificate.flow.initial_nonempty
      target_connected := m72InitialSliceConnected I }

end PoincareConjecture
