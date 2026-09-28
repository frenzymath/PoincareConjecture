import PoincareConjecture.Proofs.M36.CylindricalAngular
import Mathlib.Geometry.Manifold.Diffeomorph









set_option autoImplicit false

open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M36

noncomputable def cylindricalBoundaryLift (g₀ : StandardInitialMetric)
    (theta : UnitTwoSphere) : StandardCapSpace :=
  radialEuclideanRadius g₀ g₀.cylindrical_end.radius • theta.1

theorem cylindricalBoundaryLift_norm (g₀ : StandardInitialMetric) (theta : UnitTwoSphere) :
    ‖cylindricalBoundaryLift g₀ theta‖ = radialEuclideanRadius g₀ g₀.cylindrical_end.radius := by
  have hr := (radialEuclideanRadius_pos_iff g₀ _).mpr g₀.cylindrical_end.radius_pos
  simp [cylindricalBoundaryLift, norm_smul, abs_of_pos hr]

theorem cylindricalBoundaryLift_mem (g₀ : StandardInitialMetric) (theta : UnitTwoSphere) :
    cylindricalBoundaryLift g₀ theta ∈ g₀.cylindrical_end.carrier := by
  rw [cylindrical_carrier_eq, Set.mem_ofPred_eq, cylindricalBoundaryLift_norm,
    radialArclength_euclideanRadius]

theorem cylindricalBoundaryLift_contMDiff (g₀ : StandardInitialMetric) :
    ContMDiff (𝓡 2) (𝓡 3) ∞ (cylindricalBoundaryLift g₀) := by
  let : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) := ⟨by simp⟩
  have hs : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun _ : UnitTwoSphere => radialEuclideanRadius g₀ g₀.cylindrical_end.radius) :=
    contMDiff_const
  exact hs.smul (contMDiff_coe_sphere (E := StandardCapSpace) (n := 2))

theorem cylindricalBoundaryDirection_contMDiff (g₀ : StandardInitialMetric) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (cylindricalBoundaryDirection g₀) := by
  have hC : ContMDiff (𝓡 2) (𝓡 3) ∞
      (fun theta : UnitTwoSphere => g₀.cylindrical_end.coordinate (theta, 0)) :=
    g₀.cylindrical_end.coordinate_smooth.comp_contMDiff
      (contMDiff_id.prodMk contMDiff_const)
      (fun _ => ⟨Set.mem_univ _, neg_lt_zero.mpr g₀.cylindrical_end.collar_pos⟩)
  exact radialDirection_contMDiffOn.comp_contMDiff hC (fun theta =>
    cylindrical_coordinate_ne_zero g₀ (theta, 0) le_rfl)

noncomputable def cylindricalBoundaryInverse (g₀ : StandardInitialMetric)
    (theta : UnitTwoSphere) : UnitTwoSphere :=
  (g₀.cylindrical_end.inverse (cylindricalBoundaryLift g₀ theta)).1

theorem cylindricalBoundaryInverse_contMDiff (g₀ : StandardInitialMetric) :
    ContMDiff (𝓡 2) (𝓡 2) ∞ (cylindricalBoundaryInverse g₀) :=
  (g₀.cylindrical_end.inverse_smooth.comp_contMDiff
    (cylindricalBoundaryLift_contMDiff g₀) (cylindricalBoundaryLift_mem g₀)).fst

theorem cylindricalBoundaryLift_direction (g₀ : StandardInitialMetric)
    (theta : UnitTwoSphere) :
    cylindricalBoundaryLift g₀ (cylindricalBoundaryDirection g₀ theta) =
      g₀.cylindrical_end.coordinate (theta, 0) := by
  have hx := cylindrical_coordinate_ne_zero g₀ (theta, 0) le_rfl
  have hnorm : ‖g₀.cylindrical_end.coordinate (theta, 0)‖ =
      radialEuclideanRadius g₀ g₀.cylindrical_end.radius := by
    simpa only [add_zero] using cylindrical_coordinate_norm g₀ (theta, 0) le_rfl
  unfold cylindricalBoundaryLift cylindricalBoundaryDirection
  rw [radialDirection_val _ hx, ← hnorm]
  simp [smul_smul, norm_ne_zero_iff.mpr hx]

theorem cylindricalBoundary_left_inverse (g₀ : StandardInitialMetric) :
    Function.LeftInverse (cylindricalBoundaryInverse g₀) (cylindricalBoundaryDirection g₀) := by
  intro theta
  unfold cylindricalBoundaryInverse
  rw [cylindricalBoundaryLift_direction]
  exact congrArg Prod.fst
    (g₀.cylindrical_end.coordinate_left_inverse (x := (theta, 0)) ⟨Set.mem_univ _, by simp⟩)

theorem cylindricalBoundary_right_inverse (g₀ : StandardInitialMetric) :
    Function.RightInverse (cylindricalBoundaryInverse g₀) (cylindricalBoundaryDirection g₀) := by
  intro theta
  have hz : (g₀.cylindrical_end.inverse (cylindricalBoundaryLift g₀ theta)).2 = 0 :=
    cylindrical_inverse_boundary g₀ (by
      rw [cylindricalBoundaryLift_norm, radialArclength_euclideanRadius])
  have hC : g₀.cylindrical_end.coordinate (cylindricalBoundaryInverse g₀ theta, 0) =
      cylindricalBoundaryLift g₀ theta := by
    rw [cylindricalBoundaryInverse, ← hz]
    exact g₀.cylindrical_end.coordinate_right_inverse (cylindricalBoundaryLift_mem g₀ theta)
  unfold cylindricalBoundaryDirection
  rw [hC]
  exact radialDirection_polar g₀ (theta, g₀.cylindrical_end.radius)
    g₀.cylindrical_end.radius_pos

noncomputable def cylindricalBoundaryDiffeomorph (g₀ : StandardInitialMetric) :
    UnitTwoSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ UnitTwoSphere where
  toFun := cylindricalBoundaryDirection g₀
  invFun := cylindricalBoundaryInverse g₀
  left_inv := cylindricalBoundary_left_inverse g₀
  right_inv := cylindricalBoundary_right_inverse g₀
  contMDiff_toFun := cylindricalBoundaryDirection_contMDiff g₀
  contMDiff_invFun := cylindricalBoundaryInverse_contMDiff g₀

end PoincareConjecture.M36
