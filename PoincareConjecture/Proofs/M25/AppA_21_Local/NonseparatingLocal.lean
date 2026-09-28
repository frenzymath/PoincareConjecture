import PoincareConjecture.Proofs.M25.AppA_21_Local
import PoincareConjecture.Proofs.M25.AppA_21_Local.NonseparatingCenters
import PoincareConjecture.Proofs.M25.AppA_21_Local.NonseparatingFiniteAlternative
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.IntrinsicChainTube









set_option autoImplicit false
open Set
open scoped Manifold ContDiff Bundle ENNReal Topology
universe u
namespace PoincareConjecture.M25






theorem nonseparatingLocalInput_of_local_producers : NonseparatingLocalInput.{u} := by
  classical
  obtain ⟨ε2, h2pos, h2cap, hN2⟩ :=
    NeckOnlyCover.exists_uniform_nonseparating_center_labels.{u}
  obtain ⟨ε1, h1pos, _, hN1⟩ := N1_nonseparating_neckOnly_finite_tube_or_fibration.{u}
  obtain ⟨εt, htpos, _, htube⟩ :=
    BalancedNeckChain.exists_epsilonTubeCertificate_of_finite.{u}
  refine ⟨min ε2 (min ε1 εt), lt_min h2pos (lt_min h1pos htpos),
    (min_le_left _ _).trans h2cap, ?_⟩
  intro M _ _ _ _ _ _ g H he hcenters hwit
  obtain ⟨N0, hN0, hN0x, hN0non⟩ := hwit
  let K : NeckOnlyCover g :=
    { epsilon := H.epsilon
      epsilon_pos := H.epsilon_pos
      epsilon_threshold := H.epsilon_threshold
      epsilon_threshold_pos := H.epsilon_threshold_pos
      epsilon_threshold_le_one_two_hundred := H.epsilon_threshold_le_one_two_hundred
      epsilon_le_threshold := H.epsilon_le_threshold
      X := H.X
      connected_X := H.connected_X
      necks := {N | N ∈ H.necks ∧ N.center ∈ H.X}
      pointwise_center_cover := by
        intro x hx
        obtain ⟨N, hN, hNx⟩ := hcenters x hx
        refine ⟨N, ⟨hN, ?_⟩, hNx⟩
        rw [hNx]
        exact hx
      neck_epsilon := by
        intro N hN
        exact H.neck_epsilon N hN.1 }
  have hKnon : ∀ N ∈ K.necks, N.IsNonseparating := by
    intro N hN
    exact hN2 K (show K.epsilon ≤ ε2 from he.trans (min_le_left _ _))
      ⟨N0, show N0 ∈ H.necks ∧ N0.center ∈ H.X from ⟨hN0, hN0x⟩, hN0x, hN0non⟩
      N hN hN.2
  rcases hN1 K (show K.epsilon ≤ ε1 from
      he.trans (min_le_of_right_le (min_le_left _ _))) hKnon with
    ⟨C, a, b, hshape, hXsub⟩ | ⟨F, hFε, hFX⟩
  ·
    obtain ⟨T, hTε, -, -⟩ := htube C H.X hshape
      (show K.epsilon ≤ εt from he.trans (min_le_of_right_le (min_le_right _ _))) hXsub
    refine ⟨{ region := NeckCapRegion.tube T, compatible := ?_ }⟩
    change T.epsilon = H.epsilon
    exact hTε
  ·
    refine ⟨{ region := NeckCapRegion.fibration F, compatible := ?_ }⟩
    change F.epsilon = H.epsilon ∧ H.X ⊆ F.carrier
    exact ⟨hFε, hFX⟩

end PoincareConjecture.M25
