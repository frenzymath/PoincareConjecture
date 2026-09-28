import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.SignedAxisPermutations









set_option autoImplicit false

namespace PoincareConjecture.M76.Dehn


def reflectedCycleClosingFrame (first last frameFirst frameLast : SignedAxisPermutation) :
    SignedAxisPermutation :=
  (frameFirst.trans first).trans (frameLast.trans last).symm

theorem reflectedCycleClosingFrame_agreement
    (first last frameFirst frameLast : SignedAxisPermutation) (x : signedTubeDiamond) :
    last.diamond (frameLast.diamond
      ((reflectedCycleClosingFrame first last frameFirst frameLast).diamond x)) =
        first.diamond (frameFirst.diamond x) := by
  rw [reflectedCycleClosingFrame,
    SignedAxisPermutation.diamond_trans_apply (frameFirst.trans first) (frameLast.trans last).symm,
    ← SignedAxisPermutation.diamond_trans_apply frameLast last,
    SignedAxisPermutation.diamond_apply_symm, SignedAxisPermutation.diamond_trans_apply]


theorem exists_reflected_cycle_frames (n : ℕ)
    (left right : Fin (n + 2) → SignedAxisPermutation)
    (first last initial : SignedAxisPermutation) :
    ∃ (frame : Fin (n + 3) → SignedAxisPermutation) (closing : SignedAxisPermutation),
      frame 0 = initial ∧
      (∀ (e : Fin (n + 2)) (x : signedTubeDiamond),
        (left e).diamond ((frame e.castSucc).diamond x) =
          (right e).diamond ((frame e.succ).diamond x)) ∧
      closing = reflectedCycleClosingFrame first last (frame 0) (frame (Fin.last (n + 2))) ∧
      ∀ x : signedTubeDiamond,
        last.diamond ((frame (Fin.last (n + 2))).diamond (closing.diamond x)) =
          first.diamond ((frame 0).diamond x) := by
  let f : ℕ → SignedAxisPermutation := Nat.rec initial (fun k prev ↦
    if hk : k < n + 2 then
      (prev.trans (left ⟨k, hk⟩)).trans (right ⟨k, hk⟩).symm
    else prev)
  let frame : Fin (n + 3) → SignedAxisPermutation := fun i ↦ f i.val
  have hframe (e : Fin (n + 2)) (x : signedTubeDiamond) :
      (left e).diamond ((frame e.castSucc).diamond x) =
        (right e).diamond ((frame e.succ).diamond x) := by
    change (left e).diamond ((f e.val).diamond x) =
      (right e).diamond ((f (e.val + 1)).diamond x)
    rw [show f (e.val + 1) = ((f e.val).trans (left e)).trans (right e).symm by
      simp only [f, dif_pos e.isLt]]
    rw [SignedAxisPermutation.diamond_trans_apply,
      SignedAxisPermutation.diamond_apply_symm, SignedAxisPermutation.diamond_trans_apply]
  exact ⟨frame, reflectedCycleClosingFrame first last (frame 0) (frame (Fin.last (n + 2))),
    rfl, hframe, rfl, reflectedCycleClosingFrame_agreement _ _ _ _⟩

end PoincareConjecture.M76.Dehn
