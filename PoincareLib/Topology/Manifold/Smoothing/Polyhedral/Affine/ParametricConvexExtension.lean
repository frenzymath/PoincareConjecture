import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.ContractibleConvexExtension
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.ContractibleMappingSpace

/-!
# Continuous core extension retaining all slice parameters

Currying into a contractible compact-open mapping space extends
boundary data jointly in the core and parameter coordinates.
See Cairns 1940, pp. 804--805 and M76 derivation 56.
-/

set_option autoImplicit false

open Set

namespace ContinuousMap

variable {E B Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [TopologicalSpace B] [LocallyCompactSpace B] [TopologicalSpace Y] [ContractibleSpace Y]

/-- A continuous family of maps on a convex body's frontier
extends jointly over the body, retaining every parameter and
exact boundary values. See Cairns p. 804 and M76 derivation 56. -/
theorem exists_convexBody_parametric_extension {C : Set E}
    (hC : IsClosed C) (hc : Convex ℝ C) (hi : (interior C).Nonempty)
    (hb : Bornology.IsBounded C) (f : C(frontier C × B, Y)) :
    ∃ g : C(C × B, Y), ∀ x : frontier C, ∀ b : B,
      g (⟨x, hC.frontier_subset x.property⟩, b) = f (x, b) := by
  let : ContractibleSpace C(B, Y) := contractibleSpace_of_target B Y
  obtain ⟨g, hg⟩ := exists_convexBody_extension_of_contractible hC hc hi hb f.curry
  refine ⟨g.uncurry, ?_⟩
  intro x b
  exact congrArg (fun k : C(B, Y) => k b) (hg x)

end ContinuousMap
