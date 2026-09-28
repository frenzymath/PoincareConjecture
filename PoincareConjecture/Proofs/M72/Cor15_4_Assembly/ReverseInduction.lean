import PoincareConjecture.Proofs.M72.Cor15_4_Assembly.HistoryIndices
import PoincareConjecture.Proofs.M72.Cor15_4_Assembly.Substitution

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
  [SecondCountableTopology M]
  {N : NormalizedInitialMetric (M := M)}

theorem m72ReverseInduction
    (I : M72ReconstructionInput N) (L : M72ReconstructionLedger I)
    (e : M72EventIndex I L) :
    Nonempty (M72IndexedAssembly (m72TailSummandPiece I L e)
      (I.global.certificate.flow.slice (M72EventTopology I L e).pre_time)) := by
  classical
  refine (wellFounded_gt (α := M72EventIndex I L)).induction
    (C := fun e => Nonempty (M72IndexedAssembly (m72TailSummandPiece I L e)
      (I.global.certificate.flow.slice (M72EventTopology I L e).pre_time))) e ?_
  intro e ih
  by_cases heH : e.1 = I.extinction.extinction_time
  · let R := M72IndexedAssembly.ofAssembly (M72EventTopology I L e).conclusion.reconstruction
    exact ⟨R.reindex (m72TerminalTailEquiv I L e heH)
      (m72TerminalTailEquiv_piece I L e heH)⟩
  · have heHlt : e.1 < I.extinction.extinction_time :=
      lt_of_le_of_ne (M72EventBeforeExtinction I L e) heH
    obtain ⟨e', horder, hminimal⟩ := m72ImmediateSuccessor I L e heHlt
    obtain ⟨R⟩ := ih e' horder
    have hpred : (M72EventTopology I L e').predecessor = e.1 :=
      m72SuccessorNextPredecessor (M72EventTopology I L e') (M72EventFlowMem I L e)
        horder hminimal
    let d : Diffeomorph (𝓡 3) (𝓡 3)
        (I.global.certificate.flow.slice (M72EventTopology I L e').pre_time).carrier
        (I.global.certificate.flow.slice e.1).carrier ∞ := by
      rw [← hpred]
      exact (M72EventTopology I L e').predecessor_transport.symm
    let Rpost := R.transportTarget d
    let Rpre := (M72EventTopology I L e).conclusion.substitute Rpost
      (fun j => m72SummandPieceNonempty I L j.1)
    exact ⟨Rpre.reindex (m72SuccessorTailEquiv I L e e' horder hminimal)
      (m72SuccessorTailEquiv_piece I L e e' horder hminimal)⟩

end PoincareConjecture
