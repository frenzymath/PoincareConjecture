import PoincareConjecture.Proofs.M09.CoordinateCompatibility
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Topology
open Filter

namespace PoincareConjecture.Proofs.M09

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_coordinateFieldDerivative
    (C : ℝ × E → E →L[ℝ] E →L[ℝ] E) (x Y : ℝ → E) (s : ℝ)
    (a alpha w beta : E) (hC : DifferentiableAt ℝ C (s, x s))
    (hx : HasDerivAt x a s) (hx2 : HasDerivAt (deriv x) alpha s)
    (hY : HasDerivAt Y w s) (hY2 : HasDerivAt (deriv Y) beta s) :
    HasDerivAt (fun r ↦ deriv Y r + C (r, x r) (deriv x r) (Y r))
      (beta + (fderiv ℝ C (s, x s) (1, a) a (Y s) +
        C (s, x s) alpha (Y s) + C (s, x s) a w)) s := by
  have hcomp : HasDerivAt (C ∘ fun r : ℝ ↦ (r, x r))
      ((fderiv ℝ C (s, x s)) (1, a)) s :=
    hC.hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id s).prodMk hx)
  have hpair1 : HasDerivAt
      (fun r ↦ (C (r, x r)) (deriv x r))
      (((fderiv ℝ C (s, x s)) (1, a)) a + (C (s, x s)) alpha) s := by
    have h := hcomp.clm_apply hx2
    simpa only [Function.comp_def, hx.deriv, map_zero, add_zero] using h
  have hpair : HasDerivAt
      (fun r ↦ (C (r, x r)) (deriv x r) (Y r))
      (((fderiv ℝ C (s, x s)) (1, a)) a (Y s) +
        (C (s, x s)) alpha (Y s) + (C (s, x s)) a w) s := by
    have h := hpair1.clm_apply hY
    simpa only [hx.deriv, map_zero, add_zero, ContinuousLinearMap.add_apply] using h
  have hsum := hY2.add hpair
  convert! hsum using 1

theorem coordinate_jacobi_commutation
    (C : ℝ × E → E →L[ℝ] E →L[ℝ] E) (x Y : ℝ → E) (s : ℝ)
    (hC : DifferentiableAt ℝ C (s, x s))
    (hsym : ∀ᶠ z in 𝓝 (s, x s), ∀ v w, C z v w = C z w v)
    (hx : DifferentiableAt ℝ x s) (hx2 : DifferentiableAt ℝ (deriv x) s)
    (hY : DifferentiableAt ℝ Y s) (hY2 : DifferentiableAt ℝ (deriv Y) s) :
    let z := (s, x s)
    let a := deriv x s
    let v := Y s
    let d : ℝ → E := fun r ↦ deriv Y r + C (r, x r) (deriv x r) (Y r)
    deriv d s + C z a (d s) +
      (fderiv ℝ C z (0, v) a a - fderiv ℝ C z (0, a) v a +
        C z v (C z a a) - C z a (C z v a)) - fderiv ℝ C z (1, 0) a v =
      deriv (deriv Y) s + fderiv ℝ C z (0, v) a a +
        (2 : ℝ) • C z a (deriv Y s) + C z v (deriv (deriv x) s + C z a a) := by
  dsimp only
  rw [(hasDerivAt_coordinateFieldDerivative C x Y s _ _ _ _ hC
    hx.hasDerivAt hx2.hasDerivAt hY.hasDerivAt hY2.hasDerivAt).deriv]
  have hp : ((1, deriv x s) : ℝ × E) = (1, 0) + (0, deriv x s) := by simp
  rw [hp]
  simp only [map_add, ContinuousLinearMap.add_apply, two_smul]
  rw [fderiv_bilinear_symm C (s, x s) hC hsym (0, deriv x s) (deriv x s) (Y s),
    hsym.self_of_nhds (deriv x s) (Y s),
    hsym.self_of_nhds (deriv (deriv x) s) (Y s)]
  abel

end PoincareConjecture.Proofs.M09
