import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.SignedPathFrames









set_option autoImplicit false

namespace PoincareConjecture.M76.Dehn


def signedCycleClosingFrame (first last frameFirst frameLast : Fin 2 → Bool) : Fin 2 → Bool :=
  fun i ↦ signedTubeReindex (frameLast i)
    (signedTubeReindex (last i) (signedTubeReindex (first i) (frameFirst i)))

theorem signedCycleClosingFrame_agreement
    (first last frameFirst frameLast : Fin 2 → Bool) (x : signedTubeDiamond) :
    signedTubeDiamondReflection last (signedTubeDiamondReflection frameLast
      (signedTubeDiamondReflection (signedCycleClosingFrame first last frameFirst frameLast) x)) =
      signedTubeDiamondReflection first (signedTubeDiamondReflection frameFirst x) := by
  simp only [signedTubeDiamondReflection_comp]
  congr 1
  apply congrArg signedTubeDiamondReflection
  funext i
  dsimp only [signedCycleClosingFrame]
  cases first i <;> cases last i <;> cases frameFirst i <;> cases frameLast i <;> rfl


theorem exists_signed_cycle_frames (n : ℕ)
    (left right : Fin (n + 2) → Fin 2 → Bool)
    (first last initial : Fin 2 → Bool) :
    ∃ (frame : Fin (n + 3) → Fin 2 → Bool) (closing : Fin 2 → Bool),
      frame 0 = initial ∧
      (∀ (e : Fin (n + 2)) (i : Fin 2),
        signedTubeReindex (left e i) (frame e.castSucc i) =
          signedTubeReindex (right e i) (frame e.succ i)) ∧
      closing = signedCycleClosingFrame first last (frame 0) (frame (Fin.last (n + 2))) ∧
      ∀ x : signedTubeDiamond,
        signedTubeDiamondReflection last (signedTubeDiamondReflection (frame (Fin.last (n + 2)))
          (signedTubeDiamondReflection closing x)) =
            signedTubeDiamondReflection first (signedTubeDiamondReflection (frame 0) x) := by
  obtain ⟨frame, h0, hframe⟩ := exists_signed_path_frames (n + 1) left right initial
  exact ⟨frame, signedCycleClosingFrame first last (frame 0) (frame (Fin.last (n + 2))),
    h0, hframe, rfl, signedCycleClosingFrame_agreement _ _ _ _⟩

end PoincareConjecture.M76.Dehn
