import PoincareConjecture.Proofs.M35.Thm12_28.EuclideanCylinder









set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35



theorem cylinderEuclideanCoefficients_time_affine (u : ℝ)
    (p v w : EuclideanSpace ℝ (Fin 3)) :
    cylinderEuclideanCoefficients u p v w =
      (1 - u) * cylinderEuclideanCoefficients 0 p v w +
        u * ((cylinderCoordinateEquiv v).2 * (cylinderCoordinateEquiv w).2) := by
  rw [cylinderEuclideanCoefficients_apply, cylinderEuclideanCoefficients_apply]
  ring

private theorem coefficient_zero_smooth (v w : EuclideanSpace ℝ (Fin 3)) :
    ContDiff ℝ ∞ (fun p => cylinderEuclideanCoefficients 0 p v w) := by
  have hn : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 3) =>
      ‖(cylinderCoordinateEquiv p).1‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_fst.comp cylinderCoordinateEquiv.contDiff)
  have hf : ContDiff ℝ ∞ (fun p : EuclideanSpace ℝ (Fin 3) =>
      32 * (1 - (0 : ℝ)) / (‖(cylinderCoordinateEquiv p).1‖ ^ 2 + 4) ^ 2) :=
    contDiff_const.div ((hn.add contDiff_const).pow 2) (fun _ => ne_of_gt (by positivity))
  exact (hf.mul contDiff_const).add contDiff_const



theorem continuous_cylinder_metric_jet (r : ℕ) (p v w : EuclideanSpace ℝ (Fin 3)) :
    Continuous (fun u : ℝ => iteratedFDeriv ℝ r
      (fun y => cylinderEuclideanCoefficients u y v w) p) := by
  let f : EuclideanSpace ℝ (Fin 3) → ℝ := fun y => cylinderEuclideanCoefficients 0 y v w
  let a : EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun _ => (cylinderCoordinateEquiv v).2 * (cylinderCoordinateEquiv w).2
  have hr : (r : ℕ∞ω) ≤ ∞ := by norm_cast; exact le_top
  have hf : ContDiffAt ℝ r f p := (coefficient_zero_smooth v w).contDiffAt.of_le hr
  have ha : ContDiffAt ℝ r a p := contDiffAt_const
  have hj (u : ℝ) : iteratedFDeriv ℝ r
      (fun y => cylinderEuclideanCoefficients u y v w) p =
      (1 - u) • iteratedFDeriv ℝ r f p + u • iteratedFDeriv ℝ r a p := by
    have heq : (fun y => cylinderEuclideanCoefficients u y v w) = (1 - u) • f + u • a :=
      funext (fun y => cylinderEuclideanCoefficients_time_affine u y v w)
    rw [heq]
    have hsum := iteratedFDeriv_add_apply (f := (1 - u) • f) (g := u • a)
      (hf.const_smul (1 - u)) (ha.const_smul u)
    exact hsum.trans (congrArg₂ (· + ·) (iteratedFDeriv_const_smul_apply hf)
      (iteratedFDeriv_const_smul_apply ha))
  simp_rw [hj]
  exact ((continuous_const.sub continuous_id).smul continuous_const).add
    (continuous_id.smul continuous_const)

end PoincareConjecture.M35
