import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Analysis.Local.Angle
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.CircleLift

/-!
# Local angular coordinates in the contract plane

Morgan-Tian Definition 18.17, printed p. 430, annular regularization.
The global principal angle can be replaced near every nonzero point by
a smooth angle. Periodic maps have the same value in every such angle.
-/

set_option autoImplicit false

namespace PoincareMT

/-- Principal angle in the contract plane. Source: MT Definition
18.17, p. 430, annular regularization derivation. -/
noncomputable def m60PlaneAngle (z : LoopPlane) : ℝ :=
  Complex.arg (Complex.orthonormalBasisOneI.repr.symm z)

/-- Polar reconstruction in the contract plane, including the origin.
Source: MT Definition 18.17, p. 430. -/
theorem m60PlaneAngle_polar (z : LoopPlane) :
    ‖z‖ • Proofs.M58.angularPoint (m60PlaneAngle z) = z := by
  let e := Complex.orthonormalBasisOneI.repr.symm
  apply e.injective
  rw [e.map_smul]
  have he (t : ℝ) : e (Proofs.M58.angularPoint t) = (Circle.exp t : ℂ) :=
    congrArg Subtype.val (m60LoopCircleHomeomorphCircle_angular t)
  rw [he, Circle.coe_exp]
  change (‖z‖ : ℂ) * Complex.exp ((e z).arg * Complex.I) = e z
  rw [← e.norm_map z, Complex.norm_mul_exp_arg_mul_I]

/-- A smooth local angle reconstructs all points in polar form.
Source: MT Definition 18.17, p. 430, annular regularity derivation. -/
theorem m60_exists_contDiffAt_planeAngle {z : LoopPlane} (hz : z ≠ 0) :
    ∃ theta : LoopPlane → ℝ, ContDiffAt ℝ 1 theta z ∧
      ∀ w : LoopPlane, ‖w‖ • Proofs.M58.angularPoint (theta w) = w := by
  let e := Complex.orthonormalBasisOneI.repr.symm
  have hez : e z ≠ 0 := fun h => hz (e.injective (h.trans e.map_zero.symm))
  obtain ⟨theta, htheta, hpolar⟩ := M60.exists_contDiffAt_angle hez
  refine ⟨theta ∘ e, htheta.comp z e.toContinuousLinearEquiv.contDiff.contDiffAt, ?_⟩
  intro w
  apply e.injective
  rw [e.map_smul]
  have he (t : ℝ) : e (Proofs.M58.angularPoint t) = (Circle.exp t : ℂ) :=
    congrArg Subtype.val (m60LoopCircleHomeomorphCircle_angular t)
  rw [he, Circle.coe_exp]
  change (‖w‖ : ℂ) * Complex.exp (theta (e w) * Complex.I) = e w
  rw [← e.norm_map w]
  exact hpolar (e w)

/-- A periodic function has the same value for angles representing
the same point of the unit circle. Source: MT Definition 18.17,
p. 430, angular descent derivation. -/
theorem m60Periodic_eq_of_angularPoint_eq {E : Type*} {f : ℝ → E}
    (hf : Function.Periodic f rampPeriod) {s t : ℝ}
    (hst : Proofs.M58.angularPoint s = Proofs.M58.angularPoint t) : f s = f t := by
  have heq : Circle.exp s = Circle.exp t := by
    rw [← m60LoopCircleHomeomorphCircle_angular s,
      ← m60LoopCircleHomeomorphCircle_angular t]
    congr 1
    exact Subtype.ext hst
  obtain ⟨n, rfl⟩ := Circle.exp_eq_exp.mp heq
  exact hf.int_mul n t

end PoincareMT
