import PoincareConjecture.Proofs.M76.Brown.LocallyFlatCompactifiedBall
import PoincareConjecture.Proofs.M76.Brown.FiniteCompactificationBallPair












set_option autoImplicit false

namespace PoincareConjecture.M76




theorem hasBrownLocallyFlatSphereBalls : HasBrownLocallyFlatSphereBalls := by
  intro S hS
  obtain ⟨hS⟩ := hS
  obtain ⟨D, hD, hfront, hSD, H, hmark, hregion⟩ :=
    hS.exists_compactified_ball_homeomorph
  exact ⟨D, hD, hfront, Set.isUnitBallPair_of_onePoint_homeomorph hSD H hmark hregion⟩

end PoincareConjecture.M76
