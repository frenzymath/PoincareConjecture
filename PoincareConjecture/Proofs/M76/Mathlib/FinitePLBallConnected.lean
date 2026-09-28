import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology









set_option autoImplicit false

open Set

namespace Set

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]



theorem IsFinitePLBallPair.isConnected {d b : Set X}
    (hd : IsFinitePLBallPair E d b) : IsConnected d := by
  obtain ⟨_, C, _, hcv, hne, e, _, _⟩ := hd
  exact isConnected_iff_connectedSpace.mpr
    (e.connectedSpace_iff.mpr
      (isConnected_iff_connectedSpace.mp (hcv.isConnected (hne.mono interior_subset))))

end Set
