import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallImages

/-!
# Finite PL balls in a horizontal spherical face

The injective affine top-face inclusion transports the whole
ball and its exact boundary, with no change of model dimension.
See Alexander 1924, p. 7 and M76 derivation 247.
-/

set_option autoImplicit false

open Set Geometry

namespace Set

variable {V E F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Embedding a finite PL ball in a horizontal face retains
its model dimension and its whole explicit boundary.
See Alexander p. 7 and M76 derivation 247. -/
theorem IsFinitePLBallPair.prod_singleton {s b : Set E}
    (hs : IsFinitePLBallPair V s b) (z : F) :
    IsFinitePLBallPair V (s ×ˢ {z}) (b ×ˢ {z}) := by
  let a : E →ᴬ[ℝ] E × F :=
    (ContinuousAffineMap.id ℝ E).prod (ContinuousAffineMap.const ℝ E z)
  have ha : Function.Injective a := fun _ _ h => congrArg Prod.fst h
  have hball := hs.affine_image a ha.injOn
  change IsFinitePLBallPair V ((fun x : E => (x, z)) '' s)
    ((fun x : E => (x, z)) '' b) at hball
  simpa only [← Set.prod_singleton] using hball

end Set
