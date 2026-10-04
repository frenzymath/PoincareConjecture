import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallImages
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Coordinates.FinitePLCoordinates

/-!
# Patch and axis homeomorphisms from the same linear germ

The canonical restriction of the original continuous linear
equivalence is finite PL on every actual finite PL ball pair.
Its entire boundary and all contained-axis restrictions remain
literal images by that same map. See Hudson 1969, pp. 12--19,
Alexander 1924, pp. 6--8 and M76 derivation 286t.
-/

set_option autoImplicit false

open Set Geometry

namespace Set

variable {M E F : Type*}
  [NormedAddCommGroup M] [NormedSpace ℝ M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The actual linear germ restricts to the canonical finite
PL map of a whole patch, with its full boundary image, exact
values, all subset membership reflections, and every literal
contained-subset restriction. Applying the same theorem to
each axis interval keeps their prescribed maps unchanged.
See Alexander pp. 6--8 and M76 derivation 286t. -/
theorem IsFinitePLBallPair.linear_image_patch_data
    {d q : Set E} (hd : IsFinitePLBallPair M d q) (e : E ≃L[ℝ] F) :
    IsFinitePLBallPair M (e '' d) (e '' q) ∧
    (e.toHomeomorph.image d).IsFinitePL ∧
    (∀ x : d, (e.toHomeomorph.image d x : F) = e x) ∧
    (∀ (u : Set E) (x : d), (x : E) ∈ u ↔
      (e.toHomeomorph.image d x : F) ∈ e '' u) ∧
    ∀ (u : Set E) (hud : u ⊆ d) (x : u),
      e.toHomeomorph.image d ⟨x, hud x.property⟩ =
        ⟨e.toHomeomorph.image u x,
          image_mono hud (e.toHomeomorph.image u x).property⟩ := by
  have htarget : IsFinitePLBallPair M (e '' d) (e '' q) :=
    hd.affine_image e.toContinuousAffineEquiv.toContinuousAffineMap e.injective.injOn
  have hPL : (e.toHomeomorph.image d).IsFinitePL := by
    have hcopy := hd
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKd, _⟩, _⟩, _⟩ := hcopy
    exact ⟨e, ⟨K, hK, hKd,
      K.affineOnFaces_affine e.toContinuousAffineEquiv.toContinuousAffineMap⟩,
      fun _ => rfl⟩
  refine ⟨htarget, hPL, fun _ => rfl, ?_, ?_⟩
  · intro u x
    change (x : E) ∈ u ↔ e (x : E) ∈ e '' u
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, heq⟩
      simpa only [e.injective heq] using hy
  · intro u hud x
    apply Subtype.ext
    rfl

end Set
