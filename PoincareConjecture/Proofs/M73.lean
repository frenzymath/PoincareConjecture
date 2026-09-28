import PoincareConjecture.Statements.M73SphereFactors
import PoincareConjecture.Proofs.M73.Cor15_4.FactorKind
import PoincareConjecture.Proofs.M73.Cor15_4.SphereBundleExclusion
import PoincareConjecture.Proofs.M73.Thm1_11.KillingHopf









set_option autoImplicit false

universe u

namespace PoincareConjecture

set_option linter.style.haveILetI false in










theorem m73SphereFactors : M73SphereFactorStatement.{u} := by
  intro M _ _ _ _ _ _ _ _ _ N I C
  letI : SimplyConnectedSpace (I.global.certificate.flow.slice 0).carrier :=
    m73_sliceZero_simplyConnected I
  have hkind := m73_factor_kind I C
    (fun B hc => SurgerySphereBundle.not_simplyConnectedSpace B hc)
  refine ⟨{ factor_kind := hkind, factor_sphere := ?_ }⟩
  intro j
  have hconn : IsConnected (Set.univ : Set (C.pieces j).carrier) := by
    rw [C.piece_eq j]
    exact (M72EventTopology I C.ledger (C.summand_index j).1).conclusion.piece_connected
      (C.summand_index j).2.1
  letI : SimplyConnectedSpace (C.pieces j).carrier :=
    C.assembly.piece_simplyConnected j hconn
  have hs : Nonempty (SurgeryPositiveSpaceform (C.pieces j)) := by
    rw [C.piece_eq j]
    exact (M72EventTopology I C.ledger (C.summand_index j).1).conclusion.spaceforms
      (C.summand_index j).2.1 (hkind j)
  exact Classical.choice (Classical.choice hs).nonempty_diffeomorph_threeSphere

end PoincareConjecture
