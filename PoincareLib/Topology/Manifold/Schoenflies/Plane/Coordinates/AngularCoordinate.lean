import PoincareLib.Topology.Manifold.Schoenflies.Plane.Coordinates.CircleParameter
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Local angular coordinates in the normal tube

Section 2 of the P2 planar-transfer skeleton. The rotating argument
branch recovers the actual sphere parameter. Smoothness is restricted
to its explicit open slit-plane domain; no global real lift is used.
See `smale/derivations/2026-09-22-local-angular-coordinate.md`.
-/

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The local angular branch centered at the first coordinate;
P2 skeleton, section 2. This total function need not be globally continuous. -/
noncomputable def circleAngularCoordinate (e : ℂ ≃ₗᵢ[ℝ] E) (p : ℝ × E) : ℝ :=
  p.1 + Complex.arg (e.symm p.2 * (Circle.exp (-p.1) : ℂ))

/-- The actual branch domain is open; P2 skeleton, section 2. -/
theorem isOpen_circleAngularCoordinate_domain (e : ℂ ≃ₗᵢ[ℝ] E) :
    IsOpen {p : ℝ × E | e.symm p.2 * (Circle.exp (-p.1) : ℂ) ∈ Complex.slitPlane} := by
  apply Complex.isOpen_slitPlane.preimage
  simp only [Circle.coe_exp]
  fun_prop

/-- The angular branch is jointly smooth at every order on its actual
open domain; P2 skeleton, section 2, using the complex logarithm branch. -/
theorem contDiffOn_circleAngularCoordinate (e : ℂ ≃ₗᵢ[ℝ] E) {k : ℕ∞ω} :
    ContDiffOn ℝ k (circleAngularCoordinate e)
      {p : ℝ × E | e.symm p.2 * (Circle.exp (-p.1) : ℂ) ∈ Complex.slitPlane} := by
  have hphase : ContDiff ℝ k (fun p : ℝ × E => e.symm p.2 * (Circle.exp (-p.1) : ℂ)) := by
    simp only [Circle.coe_exp]
    exact (e.symm.contDiff.comp contDiff_snd).mul
      (((Complex.ofRealCLM.contDiff.comp contDiff_fst.neg).mul contDiff_const).cexp)
  intro p hp
  have hl := ((Complex.contDiffAt_log (n := k) hp).restrict_scalars ℝ).comp p
    hphase.contDiffAt
  have hi := Complex.imCLM.contDiff.contDiffAt.comp p hl
  change ContDiffWithinAt ℝ k
    (fun x : ℝ × E => x.1 + Complex.arg (e.symm x.2 * (Circle.exp (-x.1) : ℂ))) _ p
  simpa only [Function.comp_def, Complex.imCLM_apply,
    Complex.log_im] using
    (contDiffAt_fst.add hi).contDiffWithinAt

/-- Exponentiating the branch recovers the prescribed sphere point,
even on the cut; P2 skeleton, section 2. This is a pointwise identity. -/
theorem sphereCircleParameter_circleAngularCoordinate (e : ℂ ≃ₗᵢ[ℝ] E)
    (a : ℝ) (q : sphere (0 : E) 1) :
    sphereCircleParameter e (circleAngularCoordinate e (a, (q : E))) = q := by
  let u : Circle := ⟨e.symm (q : E), by
    exact mem_sphere_zero_iff_norm.mpr
      ((e.symm.norm_map (q : E)).trans (norm_eq_of_mem_sphere q))⟩
  have hphase : e.symm (q : E) * (Circle.exp (-a) : ℂ) =
      ((u * Circle.exp (-a) : Circle) : ℂ) := rfl
  apply Subtype.ext
  change e (Circle.exp (a + Complex.arg (e.symm (q : E) * (Circle.exp (-a) : ℂ))) : ℂ) =
    (q : E)
  rw [hphase, Circle.exp_add, Circle.exp_arg]
  have hcancel : Circle.exp a * (u * Circle.exp (-a)) = u := by
    simp [Circle.exp_neg, mul_left_comm]
  rw [hcancel]
  exact e.apply_symm_apply _

/-- The branch is the exact inverse on its half-open angular interval;
P2 skeleton, section 2. Smoothness at the upper endpoint is not asserted. -/
theorem circleAngularCoordinate_sphereCircleParameter (e : ℂ ≃ₗᵢ[ℝ] E)
    (a b : ℝ) (hab : b - a ∈ Ioc (-Real.pi) Real.pi) :
    circleAngularCoordinate e (a, (sphereCircleParameter e b : E)) = b := by
  change a + Complex.arg (e.symm (e (Circle.exp b : ℂ)) * (Circle.exp (-a) : ℂ)) = b
  rw [e.symm_apply_apply, ← Circle.coe_mul, ← Circle.exp_add,
    show b + -a = b - a by ring, Circle.arg_exp hab.1 hab.2]
  ring

/-- The open angular interval lies in the smooth branch domain;
P2 skeleton, section 2. Both branch endpoints are excluded. -/
theorem sphereCircleParameter_mem_angularDomain (e : ℂ ≃ₗᵢ[ℝ] E)
    (a b : ℝ) (hab : b - a ∈ Ioo (-Real.pi) Real.pi) :
    (a, (sphereCircleParameter e b : E)) ∈
      {p : ℝ × E | e.symm p.2 * (Circle.exp (-p.1) : ℂ) ∈ Complex.slitPlane} := by
  change e.symm (e (Circle.exp b : ℂ)) * (Circle.exp (-a) : ℂ) ∈ Complex.slitPlane
  rw [e.symm_apply_apply, ← Circle.coe_mul, ← Circle.exp_add,
    show b + -a = b - a by ring, Complex.mem_slitPlane_iff_arg,
    Circle.arg_exp hab.1 hab.2.le]
  exact ⟨hab.2.ne, Circle.coe_ne_zero _⟩

end Poincare.Manifold.Schoenflies.Plane
