import PoincareConjecture.Proofs.M38.ProjectiveAffineChart

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

open Poincare.Topology

attribute [local instance] projectiveLiftChartedSpace projective_lift_isManifold

variable (R : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))

noncomputable def projectivePolarMap (p : RoundCylinderSpace) :
    projectiveCarrier.{u}.carrier :=
  liftedProjectiveCover.cover (sphereOrthogonalDiffeomorph R (spherePolarMap p))

theorem projectiveOrthogonal_fibers (x y : UnitThreeSphere) :
    liftedProjectiveCover.{u}.cover (sphereOrthogonalDiffeomorph R x) =
        liftedProjectiveCover.cover (sphereOrthogonalDiffeomorph R y) ↔
      x = y ∨ x = -y := by
  have hinj : Function.Injective (sphereOrthogonalDiffeomorph R) :=
    (sphereOrthogonalDiffeomorph R).injective
  rw [liftedProjectiveCover.fibers, ← sphereOrthogonalDiffeomorph_neg,
    hinj.eq_iff, hinj.eq_iff]

theorem projectiveOrthogonal_center_fiber (x : UnitThreeSphere) :
    liftedProjectiveCover.{u}.cover (sphereOrthogonalDiffeomorph R x) =
        projectiveAffineMap R 0 ↔
      x = spherePolarPole 2 ∨ x = -spherePolarPole 2 := by
  change _ = liftedProjectiveCover.cover
    (sphereOrthogonalDiffeomorph R (sphereAffineMap 0)) ↔ _
  rw [sphereAffineMap_zero, projectiveOrthogonal_fibers]

theorem projectivePolar_fibers (x y : RoundCylinderSpace) :
    projectivePolarMap.{u} R x = projectivePolarMap R y ↔
      x = y ∨ x = (-y.1, -y.2) := by
  have hinj : Function.Injective (spherePolarMap : RoundCylinderSpace → UnitThreeSphere) :=
    fun x y h => (spherePolarPartialDiffeomorph 2).toPartialEquiv.injOn
      (mem_univ x) (mem_univ y) h
  change liftedProjectiveCover.cover _ = liftedProjectiveCover.cover _ ↔ _
  rw [projectiveOrthogonal_fibers, ← spherePolarMap_neg, hinj.eq_iff, hinj.eq_iff]

theorem projectivePolar_reflection (x : RoundCylinderSpace) :
    projectivePolarMap.{u} R (-x.1, -x.2) = projectivePolarMap R x :=
  (projectivePolar_fibers R _ _).mpr (Or.inr rfl)

theorem projectivePolar_ne_center (x : RoundCylinderSpace) :
    projectivePolarMap.{u} R x ≠ projectiveAffineMap R 0 := by
  intro h
  have hp := (projectiveOrthogonal_center_fiber R (spherePolarMap x)).mp h
  have hn := spherePolarMap_mem x
  change spherePolarTail (spherePolarMap x) ≠ 0 at hn
  exact hn ((spherePolarTail_eq_zero_iff _).mpr hp)

theorem projectivePolar_range : range (projectivePolarMap.{u} R) =
    {projectiveAffineMap R 0}ᶜ := by
  apply subset_antisymm
  · rintro _ ⟨x, rfl⟩
    exact projectivePolar_ne_center R x
  · intro y hy
    obtain ⟨a, ha⟩ := liftedProjectiveCover.surjective y
    let x := (sphereOrthogonalDiffeomorph R).symm a
    have hx : x ∈ spherePolarDomain 2 := by
      change spherePolarTail x ≠ 0
      intro ht
      have hp := (spherePolarTail_eq_zero_iff x).mp ht
      have he := (projectiveOrthogonal_center_fiber R x).mpr hp
      rw [show sphereOrthogonalDiffeomorph R x = a from
        (sphereOrthogonalDiffeomorph R).apply_symm_apply a, ha] at he
      exact hy he
    refine ⟨spherePolarInverse ⟨x, hx⟩, ?_⟩
    change liftedProjectiveCover.cover
      (sphereOrthogonalDiffeomorph R (spherePolarMap (spherePolarInverse ⟨x, hx⟩))) = y
    rw [spherePolar_right_inv]
    exact ((congrArg liftedProjectiveCover.cover
      ((sphereOrthogonalDiffeomorph R).apply_symm_apply a)).trans ha)

theorem projectivePolar_localDiffeomorph :
    IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (projectivePolarMap.{u} R) := by
  intro x
  exact (((spherePolarPartialDiffeomorph 2).isLocalDiffeomorphAt
    ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (mem_univ x)).comp
      (𝓡 3) UnitThreeSphere ((sphereOrthogonalDiffeomorph R).isLocalDiffeomorph _)).comp
        (𝓡 3) projectiveCarrier.carrier (liftedProjectiveCover.local_diffeomorph _)

theorem projectivePolar_affine (z : UnitTwoSphere) {t : ℝ} (ht : 0 < t) :
    projectivePolarMap.{u} R (z, t) = projectiveAffineMap R (t⁻¹ • z.val) := by
  have hv : sphereAffineVector (t⁻¹ • z.val) = t⁻¹ • spherePolarVector (z, t) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change 1 = t⁻¹ * t
      exact (inv_mul_cancel₀ ht.ne').symm
    · rfl
  have hn : ‖sphereAffineVector (t⁻¹ • z.val)‖ = t⁻¹ * ‖spherePolarVector (z, t)‖ := by
    rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
  have hs : sphereAffineMap (t⁻¹ • z.val) = spherePolarMap (z, t) := by
    apply Subtype.ext
    change ‖sphereAffineVector (t⁻¹ • z.val)‖⁻¹ •
      sphereAffineVector (t⁻¹ • z.val) = _
    rw [hn, hv, mul_inv_rev, inv_inv, smul_smul, mul_assoc,
      mul_inv_cancel₀ ht.ne', mul_one]
    rfl
  exact congrArg (fun a => liftedProjectiveCover.cover (sphereOrthogonalDiffeomorph R a)) hs.symm

end PoincareConjecture.M38
