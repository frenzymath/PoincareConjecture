import PoincareConjecture.Proofs.M76.Mathlib.RadialBallQuotient









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




noncomputable def radialClosedBallMap (f : C(sphere (0 : E) 1, sphere (0 : F) 1)) :
    C(closedBall (0 : E) 1, closedBall (0 : F) 1) :=
  (isQuotientMap_unitSphereRadialMap E).lift (sphereRadialCoordinates f)
    (sphereRadialCoordinates_factors f)



theorem radialClosedBallMap_apply_radial (f : C(sphere (0 : E) 1, sphere (0 : F) 1))
    (z : I × sphere (0 : E) 1) :
    f.radialClosedBallMap (unitSphereRadialMap E z) = unitSphereRadialMap F (z.1, f z.2) := by
  exact congrArg (fun g : C(I × sphere (0 : E) 1, closedBall (0 : F) 1) => g z)
    ((isQuotientMap_unitSphereRadialMap E).lift_comp (sphereRadialCoordinates f)
      (sphereRadialCoordinates_factors f))



theorem norm_radialClosedBallMap (f : C(sphere (0 : E) 1, sphere (0 : F) 1))
    (x : closedBall (0 : E) 1) : ‖(f.radialClosedBallMap x : F)‖ = ‖(x : E)‖ := by
  obtain ⟨z, rfl⟩ := surjective_unitSphereRadialMap E x
  rw [radialClosedBallMap_apply_radial, norm_unitSphereRadialMap, norm_unitSphereRadialMap]



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



theorem radialClosedBallExtension_apply_sphere
    (e : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1) (x : sphere (0 : E) 1) :
    e.radialClosedBallExtension ⟨x, sphere_subset_closedBall x.property⟩ =
      ⟨e x, sphere_subset_closedBall (e x).property⟩ :=
  ContinuousMap.radialClosedBallMap_apply_sphere _ x



theorem norm_radialClosedBallExtension
    (e : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1) (x : closedBall (0 : E) 1) :
    ‖(e.radialClosedBallExtension x : F)‖ = ‖(x : E)‖ :=
  ContinuousMap.norm_radialClosedBallMap _ x

end Homeomorph
