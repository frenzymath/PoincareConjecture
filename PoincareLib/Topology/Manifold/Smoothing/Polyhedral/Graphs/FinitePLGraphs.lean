import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallImages

/-!
# Finite PL graph embeddings

The identity in the first coordinate makes every graph map
injective. Its affine formulas transport finite PL ball pairs
with their complete specified boundaries. See Hudson 1969,
pp. 15--19 and the attachment caps in M76 derivation 128.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The graph map of a finite piecewise-affine map is finite
piecewise-affine on the same exact domain. See Hudson pp. 15--17
and M76 derivation 128. -/
theorem FinitePiecewiseAffineOn.graph {f : E → F} {s : Set E}
    (hf : FinitePiecewiseAffineOn f s) :
    FinitePiecewiseAffineOn (fun x => (x, f x)) s := by
  obtain ⟨K, hK, rfl, hfaces⟩ := hf
  refine ⟨K, hK, rfl, fun r hr => ?_⟩
  obtain ⟨a, ha⟩ := hfaces r hr
  exact ⟨(ContinuousAffineMap.id ℝ E).prod a, fun x hx => Prod.ext rfl (ha hx)⟩

end Geometry

namespace Set

/-- Graph inclusion transports a finite PL ball pair with the
exact graph of its boundary. See Hudson pp. 15--19 and the cap
construction in M76 derivation 128. -/
theorem IsFinitePLBallPair.graph {V E F : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {s b : Set E} (hs : IsFinitePLBallPair V s b)
    {f : E → F} (hf : FinitePiecewiseAffineOn f s) :
    IsFinitePLBallPair V ((fun x => (x, f x)) '' s) ((fun x => (x, f x)) '' b) :=
  hs.image hf.graph (fun _ _ _ _ h => congrArg Prod.fst h)

end Set
