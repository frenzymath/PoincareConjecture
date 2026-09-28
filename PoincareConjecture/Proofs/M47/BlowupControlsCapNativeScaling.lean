import PoincareConjecture.Proofs.M47.BlowupControlsCapModelParallel
import PoincareConjecture.Proofs.M47.CanonicalNeckAxialJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff BigOperators Topology

namespace PoincareConjecture.M47

open Proofs.M47

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "V" => RoundCylinderCoordinates

theorem cap_native_derivative_linear
    (u : ℝ) (q : UnitTwoSphere) {r : ℕ}
    (T S : V → (Fin r → Fin 3) → ℝ) (alpha beta : ℝ) (p : V)
    (hT : ∀ a, DifferentiableAt ℝ (fun y => T y a) p)
    (hS : ∀ a, DifferentiableAt ℝ (fun y => S y a) p)
    (a : Fin (r + 1) → Fin 3) :
    roundCylinderTensorDerivative u (chartAt E2 q)
        (fun y b => alpha * T y b + beta * S y b) p a =
      alpha * roundCylinderTensorDerivative u (chartAt E2 q) T p a +
        beta * roundCylinderTensorDerivative u (chartAt E2 q) S p a := by
  unfold roundCylinderTensorDerivative
  rw [fderiv_fun_add ((hT _).const_mul alpha) ((hS _).const_mul beta),
    fderiv_const_mul (hT _) alpha, fderiv_const_mul (hS _) beta]
  simp only [add_apply, smul_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib]
  have hα (c v : ℝ) : c * (alpha * v) = alpha * (c * v) := by ring
  have hβ (c v : ℝ) : c * (beta * v) = beta * (c * v) := by ring
  simp_rw [hα, hβ, ← Finset.mul_sum]
  ring

theorem cap_native_iterated_scalar_mul_succ
    (beta u : ℝ) (hu : u < 1) (B : RoundCylinderTwoTensor)
    (q : UnitTwoSphere) {U : Set V} (hU : IsOpen U)
    (hB : ∀ i j : Fin 3, ContDiffOn ℝ ∞
      (fun y => roundCylinderTensorCoefficient B (chartAt E2 q) y i j) U)
    (k : ℕ) (p : V) (hp : p ∈ U) (a : Fin (2 + (k + 1)) → Fin 3) :
    roundCylinderIteratedDerivative u (chartAt E2 q)
        (fun z v w => beta * B z v w) (k + 1) p a =
      beta * roundCylinderIteratedDerivative u (chartAt E2 q) B (k + 1) p a := by
  have hsmooth (j : ℕ) (b : Fin (2 + j) → Fin 3) (y : V) (hy : y ∈ U) :
      ContDiffAt ℝ ∞ (fun z => roundCylinderIteratedDerivative u (chartAt E2 q) B j z b) y :=
    M34.roundCylinderIteratedDerivative_contDiffAt hu q
      (fun i l => ((hB i l).contDiffAt (hU.mem_nhds hy)).sub
        (M35.contDiff_roundCylinderGram u q i l).contDiffAt) j b
  induction k generalizing p with
  | zero =>
    have heq : roundCylinderIteratedDerivative u (chartAt E2 q)
        (fun z v w => beta * B z v w) 0 = fun y b =>
      beta * roundCylinderIteratedDerivative u (chartAt E2 q) B 0 y b +
        (beta - 1) * roundCylinderGram u (chartAt E2 q) y (b 0) (b 1) := by
      funext y b
      simp only [roundCylinderIteratedDerivative, roundCylinderTensorCoefficient]
      ring
    change roundCylinderTensorDerivative u (chartAt E2 q)
      (roundCylinderIteratedDerivative u (chartAt E2 q)
        (fun z v w => beta * B z v w) 0) p a = _
    rw [heq, cap_native_derivative_linear u q _ _ beta (beta - 1) p
      (fun b => (hsmooth 0 b p hp).differentiableAt (by simp))
      (fun b => (M35.contDiff_roundCylinderGram u q (b 0) (b 1)).differentiable
        (by simp) p) a, cap_native_modelGram_derivative_zero u hu q p a]
    simp only [mul_zero, add_zero]
    rfl
  | succ k ih =>
    have heq (b : Fin (2 + (k + 1)) → Fin 3) :
        (fun y => roundCylinderIteratedDerivative u (chartAt E2 q)
          (fun z v w => beta * B z v w) (k + 1) y b) =ᶠ[𝓝 p]
        fun y => beta * roundCylinderIteratedDerivative u (chartAt E2 q) B (k + 1) y b := by
      filter_upwards [hU.mem_nhds hp] with y hy
      exact ih y hy b
    change roundCylinderTensorDerivative u (chartAt E2 q)
        (roundCylinderIteratedDerivative u (chartAt E2 q)
          (fun z v w => beta * B z v w) (k + 1)) p a = _
    rw [roundCylinderTensorDerivative_eq_of_eventuallyEq u q heq]
    have h := cap_native_derivative_linear u q
      (roundCylinderIteratedDerivative u (chartAt E2 q) B (k + 1)) (fun _ _ => 0)
      beta 0 p (fun b => (hsmooth (k + 1) b p hp).differentiableAt (by simp))
      (fun _ => differentiableAt_const (0 : ℝ)) a
    simpa only [mul_zero, zero_mul, add_zero, roundCylinderIteratedDerivative] using h

end PoincareConjecture.M47
