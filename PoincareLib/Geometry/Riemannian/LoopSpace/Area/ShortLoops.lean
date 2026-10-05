import PoincareLib.Geometry.Riemannian.LoopSpace.ShortLoops.Main
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Filling
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Theory

/-!
# M60 checked predecessor applications

This file contains only small typed adapters. The substantial M60 analytic,
variational and flow argument remains the single admission in `Proofs/M60.lean`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

/-- Apply the corrected M58 disk threshold and the checked infimum comparison
to obtain M60's short-loop area conclusion. -/
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

end PoincareMT
