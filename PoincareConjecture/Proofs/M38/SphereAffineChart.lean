import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import PoincareConjecture.Definitions.Ch12.StandardCap
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Sphere.Polar

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

open Poincare.Topology

private instance sphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

def sphereAffineVector (x : StandardCapSpace) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 (Fin.cons 1 x)

theorem sphereAffineVector_ne_zero (x : StandardCapSpace) : sphereAffineVector x ≠ 0 := by
  intro h
  have he := congrArg (fun v : EuclideanSpace ℝ (Fin 4) => v 0) h
  norm_num [sphereAffineVector] at he

noncomputable def sphereAffineMap (x : StandardCapSpace) : UnitThreeSphere :=
  ⟨‖sphereAffineVector x‖⁻¹ • sphereAffineVector x, by
    simp only [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sphereAffineVector_ne_zero x))⟩

noncomputable def sphereAffineInverse (y : UnitThreeSphere) : StandardCapSpace :=
  (y.val 0)⁻¹ • spherePolarTail y

theorem sphereAffineMap_positive (x : StandardCapSpace) : 0 < (sphereAffineMap x).val 0 := by
  change 0 < ‖sphereAffineVector x‖⁻¹ * 1
  simpa only [mul_one] using inv_pos.mpr (norm_pos_iff.mpr (sphereAffineVector_ne_zero x))

theorem sphereAffine_left_inverse (x : StandardCapSpace) :
    sphereAffineInverse (sphereAffineMap x) = x := by
  have ht : spherePolarTail (sphereAffineMap x) = ‖sphereAffineVector x‖⁻¹ • x := by
    ext i
    rfl
  change (‖sphereAffineVector x‖⁻¹ * 1)⁻¹ • spherePolarTail (sphereAffineMap x) = x
  rw [mul_one, inv_inv, ht, smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr (sphereAffineVector_ne_zero x)), one_smul]

theorem sphereAffine_right_inverse (y : UnitThreeSphere) (hy : 0 < y.val 0) :
    sphereAffineMap (sphereAffineInverse y) = y := by
  have hv : sphereAffineVector (sphereAffineInverse y) = (y.val 0)⁻¹ • y.val := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change 1 = (y.val 0)⁻¹ * y.val 0
      exact (inv_mul_cancel₀ hy.ne').symm
    · rfl
  have hn : ‖sphereAffineVector (sphereAffineInverse y)‖ = (y.val 0)⁻¹ := by
    rw [hv, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hy),
      norm_eq_of_mem_sphere y, mul_one]
  apply Subtype.ext
  change ‖sphereAffineVector (sphereAffineInverse y)‖⁻¹ •
    sphereAffineVector (sphereAffineInverse y) = y.val
  rw [hn, inv_inv, hv, smul_smul, mul_inv_cancel₀ hy.ne', one_smul]

theorem sphereAffineVector_smooth :
    ContMDiff (𝓡 3) (𝓡 4) ∞ sphereAffineVector := by
  apply (EuclideanSpace.equiv (Fin 4) ℝ).symm.contDiff.contMDiff.comp
  apply contMDiff_pi_space.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact contMDiff_const
  · exact (ContinuousLinearMap.proj j).contMDiff.comp
      (EuclideanSpace.equiv (Fin 3) ℝ).contDiff.contMDiff

theorem sphereAffineMap_smooth : ContMDiff (𝓡 3) (𝓡 3) ∞ sphereAffineMap := by
  have hn : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun x => ‖sphereAffineVector x‖) := by
    intro x
    exact (contDiffAt_norm ℝ (sphereAffineVector_ne_zero x)).contMDiffAt.comp x
      (sphereAffineVector_smooth x)
  exact ((hn.inv₀ (fun x => norm_ne_zero_iff.mpr (sphereAffineVector_ne_zero x))).smul
    sphereAffineVector_smooth).codRestrict_sphere _

theorem sphere_first_coordinate_smooth :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun y : UnitThreeSphere => y.val 0) :=
  (ContinuousLinearMap.proj 0).contMDiff.comp
    ((EuclideanSpace.equiv (Fin 4) ℝ).contDiff.contMDiff.comp contMDiff_coe_sphere)

theorem sphereAffineInverse_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ sphereAffineInverse
    {y : UnitThreeSphere | 0 < y.val 0} := by
  apply (sphere_first_coordinate_smooth.contMDiffOn.inv₀ (fun y hy => ne_of_gt hy)).smul
    contMDiff_spherePolarTail.contMDiffOn

noncomputable def sphereAffineChart :
    PartialDiffeomorph (𝓡 3) (𝓡 3) StandardCapSpace UnitThreeSphere ∞ where
  toFun := sphereAffineMap
  invFun := sphereAffineInverse
  source := univ
  target := {y | 0 < y.val 0}
  map_source' := fun x _ => sphereAffineMap_positive x
  map_target' := fun _ _ => mem_univ _
  left_inv' := fun x _ => sphereAffine_left_inverse x
  right_inv' := sphereAffine_right_inverse
  open_source := isOpen_univ
  open_target := isOpen_lt continuous_const sphere_first_coordinate_smooth.continuous
  contMDiffOn_toFun := sphereAffineMap_smooth.contMDiffOn
  contMDiffOn_invFun := sphereAffineInverse_smooth

end PoincareConjecture.M38
