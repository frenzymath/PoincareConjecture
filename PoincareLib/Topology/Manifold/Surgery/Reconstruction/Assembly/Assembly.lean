import PoincareLib.Topology.Manifold.Surgery.Reconstruction.Assembly.FirstEvent
import PoincareLib.Topology.Manifold.Surgery.Reconstruction.Assembly.ReverseInduction

/-!
# Corollary 15.4: finite per-surgery reconstruction conclusion

The finite-history assembly supplies its own bijective enumeration of every
event non-survivor piece.  Immediate successor transports and the initial
carrier properties complete the exact M72 conclusion.
Source: Morgan--Tian Proposition 15.3 and Corollary 15.4, pp. 357--359.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
  [SecondCountableTopology M]
  {N : NormalizedInitialMetric (M := M)}

/-- Assemble the exact M72 output from local surgery topology and finite
extinction.  Source: Corollary 15.4, printed pp. 358--359. -/
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

end PoincareMT
