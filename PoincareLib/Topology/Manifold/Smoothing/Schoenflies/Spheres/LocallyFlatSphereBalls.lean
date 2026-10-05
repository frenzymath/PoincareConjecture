import PoincareLib.Topology.Manifold.Smoothing.Schoenflies.Regions.LocallyFlatCompactifiedBall
import PoincareLib.Topology.Manifold.Smoothing.Schoenflies.Regions.FiniteCompactificationBallPair

/-!
# Brown's exact locally flat sphere-ball input

The original pointwise flattening charts construct the bicollar and
bounded complementary region. The actual end quotient constructs
both cellular fibers and the supported cancellation. Restricting its
ambient compactification homeomorphism gives the exact finite ball
pair with the original whole ambient frontier.
See Brown1960 Theorems2--5, Brown1962 collars, and Brown derivation018.
-/

set_option autoImplicit false

namespace PoincareMT.M76

/-- Brown's locally flat Schoenflies conclusion with the literal
compact carrier, complete original frontier, and exact unit-ball
pair required by the frozen geometric input. -/
theorem hasBrownLocallyFlatSphereBalls : HasBrownLocallyFlatSphereBalls := by
  intro S hS
  obtain ⟨hS⟩ := hS
  obtain ⟨D, hD, hfront, hSD, H, hmark, hregion⟩ :=
    hS.exists_compactified_ball_homeomorph
  exact ⟨D, hD, hfront, Set.isUnitBallPair_of_onePoint_homeomorph hSD H hmark hregion⟩

end PoincareMT.M76
