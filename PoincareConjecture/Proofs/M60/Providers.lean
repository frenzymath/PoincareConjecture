import PoincareConjecture.Proofs.M58
import PoincareConjecture.Proofs.M60.Filling
import PoincareConjecture.Statements.M60Area

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

theorem m60ShortLoopAreaClaim_from_M58
    (P58 : RepairedShortLoopTrivialityTheory.{u}) :
    M60ShortLoopAreaClaim.{u} := by
  intro M _ _ _ _ _ g hcompact η hη
  obtain ⟨ζ, hζ, hζη, hsmall⟩ :=
    P58.short_loop.small_loop_filling g hcompact η hη
  refine ⟨ζ, hζ, hζη, ?_⟩
  intro γ hγ
  obtain ⟨D, hD⟩ := hsmall γ hγ
  refine ⟨D, hD, m60FillingArea_le_disk g γ D, ?_⟩
  exact (m60FillingArea_le_disk g γ D).trans_lt hD

end PoincareConjecture
