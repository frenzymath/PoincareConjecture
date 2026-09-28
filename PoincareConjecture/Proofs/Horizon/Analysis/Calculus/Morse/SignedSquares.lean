import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Pow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff

namespace Poincare.Analysis.Calculus.Morse

theorem contDiff_diagonal_quadratic {n : Nat} (c : Real) (σ : Fin n -> Real) :
    ContDiff Real ∞ (fun x : EuclideanSpace Real (Fin n) => c + ∑ i, σ i * x i ^ 2) :=
  contDiff_const.add (ContDiff.sum (fun i _ =>
    contDiff_const.mul ((EuclideanSpace.proj (𝕜 := Real) i).contDiff.pow 2)))

theorem fderiv_diagonal_quadratic_eq_zero_iff {n : Nat} (c : Real)
    (σ : Fin n -> Real) (hσ : ∀ i, σ i ≠ 0) (x : EuclideanSpace Real (Fin n)) :
    fderiv Real (fun y : EuclideanSpace Real (Fin n) => c + ∑ i, σ i * y i ^ 2) x = 0 ↔
      x = 0 := by
  have hd : HasFDerivAt (fun y : EuclideanSpace Real (Fin n) => c + ∑ i, σ i * y i ^ 2)
      (∑ i : Fin n, (σ i * (2 * x i)) • EuclideanSpace.proj (𝕜 := Real) i) x := by
    apply HasFDerivAt.const_add c
    convert HasFDerivAt.sum (u := Finset.univ) (fun i _ =>
      ((EuclideanSpace.proj (𝕜 := Real) i).hasFDerivAt.pow 2).const_mul (σ i)) using 1
    · ext y
      simp
    · simp [smul_smul]
  rw [hd.fderiv]
  constructor
  · intro hz
    ext i
    have hi := congrArg (fun L : EuclideanSpace Real (Fin n) →L[Real] Real =>
      L (EuclideanSpace.single i 1)) hz
    simp [EuclideanSpace.proj] at hi
    exact hi.resolve_left (hσ i)
  · rintro rfl
    simp

end Poincare.Analysis.Calculus.Morse
