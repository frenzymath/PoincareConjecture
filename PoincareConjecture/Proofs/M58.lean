import PoincareConjecture.Statements.M58LoopSmoothing
import PoincareConjecture.Proofs.M58.Lemma18_27_Triviality
import PoincareConjecture.Proofs.M58.Cor18_28_SmallDisks




















set_option autoImplicit false

universe u

namespace PoincareConjecture



theorem repairedShortLoopTriviality : RepairedShortLoopTrivialityTheory.{u} := by
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · intro M _ _ _ _ _ g hcompact basepoint hpi
    exact Proofs.M58.short_loop_family_trivial g hcompact basepoint hpi
  · intro M _ _ _ _ _ g hcompact hconnected basepoint hpi
    obtain ⟨ζ, hζ, hfamily⟩ :=
      Proofs.M58.raw_short_loop_family_trivial g hcompact hconnected basepoint hpi
    exact ⟨ζ, hζ, fun source _ hlength => hfamily source hlength⟩
  · intro M _ _ _ _ _ g hcompact η hη
    exact Proofs.M58.small_loop_filling g hcompact η hη

end PoincareConjecture
