import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.ContractibleBallExtension
import Mathlib.Analysis.Convex.GaugeRescale

/-!
# Extending frontier maps across convex cores

Gauge coordinates carry a bounded convex body's closure and frontier
to the closed ball and sphere. Thus maps into a contractible target
extend across the body with exact boundary agreement. See Cairns
1940, Section 8, p. 804, and M76 derivation 43.
-/

set_option autoImplicit false

open Set Metric

namespace ContinuousMap

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [TopologicalSpace Y] [ContractibleSpace Y]

/-- Every continuous frontier map of a closed bounded convex
body with nonempty interior extends across the body into the same
contractible target. Apply this in a core's affine span.
See Cairns p. 804 and M76 derivation 43. -/
theorem exists_convexBody_extension_of_contractible {s : Set E}
    (hs : IsClosed s) (hc : Convex ℝ s) (hi : (interior s).Nonempty)
    (hb : Bornology.IsBounded s) (f : C(frontier s, Y)) :
    ∃ g : C(s, Y), ∀ x : frontier s, g ⟨x, hs.frontier_subset x.property⟩ = f x := by
  obtain ⟨e, _, heclosure, hefrontier⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hi hb
  have hes : e '' s = closedBall (0 : E) 1 := by
    simpa only [hs.closure_eq] using heclosure
  let a : frontier s ≃ₜ sphere (0 : E) 1 :=
    (e.image (frontier s)).trans (Homeomorph.setCongr hefrontier)
  let b : s ≃ₜ closedBall (0 : E) 1 :=
    (e.image s).trans (Homeomorph.setCongr hes)
  obtain ⟨g, hg⟩ := (f.comp ⟨a.symm, a.symm.continuous⟩).exists_closedBall_extension_of_contractible
  refine ⟨g.comp ⟨b, b.continuous⟩, ?_⟩
  intro x
  have hcomm : b ⟨x, hs.frontier_subset x.property⟩ =
      ⟨a x, sphere_subset_closedBall (a x).property⟩ := Subtype.ext rfl
  change g (b ⟨x, hs.frontier_subset x.property⟩) = f x
  rw [hcomm, hg]
  exact congrArg f (a.symm_apply_apply x)

end ContinuousMap
