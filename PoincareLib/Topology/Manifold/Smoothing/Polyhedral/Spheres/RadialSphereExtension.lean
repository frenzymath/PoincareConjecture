import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.RadialBallQuotient

/-!
# Radial extensions of sphere maps and homeomorphisms

A sphere map descends through radial quotient coordinates to a
norm-preserving closed-ball map. Inverse sphere maps descend to
inverse ball maps. See Hamilton 1976, pp. 66--68 and M76 derivation 115.
-/

set_option autoImplicit false

open Set Metric unitInterval NormedSpace

namespace ContinuousMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private noncomputable def sphereRadialCoordinates (f : C(sphere (0 : E) 1, sphere (0 : F) 1)) :
    C(I × sphere (0 : E) 1, closedBall (0 : F) 1) :=
  (unitSphereRadialMap F).comp ((ContinuousMap.id I).prodMap f)

private theorem sphereRadialCoordinates_factors
    (f : C(sphere (0 : E) 1, sphere (0 : F) 1)) :
    Function.FactorsThrough (sphereRadialCoordinates f) (unitSphereRadialMap E) := by
  intro z w hzw
  obtain ⟨ht, hz | hu⟩ := (unitSphereRadialMap_eq_iff E z w).mp hzw
  · apply (unitSphereRadialMap_eq_iff F (z.1, f z.2) (w.1, f w.2)).mpr
    exact ⟨ht, Or.inl hz⟩
  · apply (unitSphereRadialMap_eq_iff F (z.1, f z.2) (w.1, f w.2)).mpr
    exact ⟨ht, Or.inr (congrArg f hu)⟩

variable [ProperSpace E] [Nontrivial E]

/-- Radially extend a continuous map of unit spheres over the
closed unit balls by descending the radial quotient. See M76
derivation 115 and Hamilton pp. 66--68. -/
noncomputable def radialClosedBallMap (f : C(sphere (0 : E) 1, sphere (0 : F) 1)) :
    C(closedBall (0 : E) 1, closedBall (0 : F) 1) :=
  (isQuotientMap_unitSphereRadialMap E).lift (sphereRadialCoordinates f)
    (sphereRadialCoordinates_factors f)

/-- Radial extension keeps the radius and applies the given
map to the sphere coordinate. See M76 derivation 115. -/
theorem radialClosedBallMap_apply_radial (f : C(sphere (0 : E) 1, sphere (0 : F) 1))
    (z : I × sphere (0 : E) 1) :
    f.radialClosedBallMap (unitSphereRadialMap E z) = unitSphereRadialMap F (z.1, f z.2) := by
  exact congrArg (fun g : C(I × sphere (0 : E) 1, closedBall (0 : F) 1) => g z)
    ((isQuotientMap_unitSphereRadialMap E).lift_comp (sphereRadialCoordinates f)
      (sphereRadialCoordinates_factors f))

/-- Radial extension preserves the norm everywhere in the
closed ball, including the origin. See M76 derivation 115. -/
theorem norm_radialClosedBallMap (f : C(sphere (0 : E) 1, sphere (0 : F) 1))
    (x : closedBall (0 : E) 1) : ‖(f.radialClosedBallMap x : F)‖ = ‖(x : E)‖ := by
  obtain ⟨z, rfl⟩ := surjective_unitSphereRadialMap E x
  rw [radialClosedBallMap_apply_radial, norm_unitSphereRadialMap, norm_unitSphereRadialMap]

/-- The closed-ball extension agrees exactly with the original
map on the included unit sphere. See M76 derivation 115. -/
theorem radialClosedBallMap_apply_sphere (f : C(sphere (0 : E) 1, sphere (0 : F) 1))
    (x : sphere (0 : E) 1) :
    f.radialClosedBallMap ⟨x, sphere_subset_closedBall x.property⟩ =
      ⟨f x, sphere_subset_closedBall (f x).property⟩ := by
  have hx : unitSphereRadialMap E (1, x) = ⟨x, sphere_subset_closedBall x.property⟩ :=
    Subtype.ext (one_smul ℝ (x : E))
  rw [← hx, radialClosedBallMap_apply_radial]
  exact Subtype.ext (one_smul ℝ (f x : F))

end ContinuousMap

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [Nontrivial E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F] [Nontrivial F]

/-- A homeomorphism of unit spheres extends radially to a
homeomorphism of closed unit balls. See Hamilton pp. 66--68
and M76 derivation 115. -/
noncomputable def radialClosedBallExtension (e : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1) :
    closedBall (0 : E) 1 ≃ₜ closedBall (0 : F) 1 where
  toFun := (e : C(sphere (0 : E) 1, sphere (0 : F) 1)).radialClosedBallMap
  invFun := (e.symm : C(sphere (0 : F) 1, sphere (0 : E) 1)).radialClosedBallMap
  left_inv x := by
    obtain ⟨z, rfl⟩ := surjective_unitSphereRadialMap E x
    simp only [ContinuousMap.radialClosedBallMap_apply_radial]
    change unitSphereRadialMap E (z.1, e.symm (e z.2)) = unitSphereRadialMap E (z.1, z.2)
    rw [e.symm_apply_apply]
  right_inv y := by
    obtain ⟨z, rfl⟩ := surjective_unitSphereRadialMap F y
    simp only [ContinuousMap.radialClosedBallMap_apply_radial]
    change unitSphereRadialMap F (z.1, e (e.symm z.2)) = unitSphereRadialMap F (z.1, z.2)
    rw [e.apply_symm_apply]
  continuous_toFun := ContinuousMap.continuous _
  continuous_invFun := ContinuousMap.continuous _

/-- The radial homeomorphism extends the prescribed boundary
homeomorphism exactly. See M76 derivation 115. -/
theorem radialClosedBallExtension_apply_sphere
    (e : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1) (x : sphere (0 : E) 1) :
    e.radialClosedBallExtension ⟨x, sphere_subset_closedBall x.property⟩ =
      ⟨e x, sphere_subset_closedBall (e x).property⟩ :=
  ContinuousMap.radialClosedBallMap_apply_sphere _ x

/-- The radial homeomorphism preserves each point's distance
from the center. See M76 derivation 115. -/
theorem norm_radialClosedBallExtension
    (e : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1) (x : closedBall (0 : E) 1) :
    ‖(e.radialClosedBallExtension x : F)‖ = ‖(x : E)‖ :=
  ContinuousMap.norm_radialClosedBallMap _ x

end Homeomorph
