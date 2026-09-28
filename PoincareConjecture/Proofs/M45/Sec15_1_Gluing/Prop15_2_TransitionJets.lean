import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_PointJetBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.TransitionBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M45

open CoordinateTransition

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem finitePointJetBounded_of_christoffel_hessian
    {ι : Type*} {l : Filter ι} {x : ι → E} {f : ι → E → E}
    {A B : ι → E → ChristoffelSpace E}
    (hf : ∀ i, ContDiffAt ℝ ∞ (f i) (x i))
    (hA : ∀ i, ContDiffAt ℝ ∞ (A i) (x i))
    (hB : ∀ i, ContDiffAt ℝ ∞ (B i) (f i (x i)))
    (hAj : ∀ m, FinitePointJetBounded m A x l)
    (hBj : ∀ m, FinitePointJetBounded m B (fun i => f i (x i)) l)
    (hzero : l.IsBoundedUnder (· ≤ ·) (fun i => ‖f i (x i)‖))
    (hfirst : l.IsBoundedUnder (· ≤ ·) (fun i => ‖fderiv ℝ (f i) (x i)‖))
    (hEq : ∀ i, fderiv ℝ (fderiv ℝ (f i)) =ᶠ[𝓝 (x i)]
      fun y => transitionHessianPolynomial (A i y, (B i (f i y), fderiv ℝ (f i) y))) :
    ∀ m, FinitePointJetBounded m f x l := by
  let D := fun i => fderiv ℝ (f i)
  have hD : ∀ i, ContDiffAt ℝ ∞ (D i) (x i) :=
    fun i => (hf i).fderiv_right (by simp)
  have hBf : ∀ i, ContDiffAt ℝ ∞ (fun y => B i (f i y)) (x i) :=
    fun i => (hB i).comp (x i) (hf i)
  have hDj : ∀ m, FinitePointJetBounded m D x l := by
    intro m
    induction m with
    | zero => exact FinitePointJetBounded.zero hfirst
    | succ m ih =>
        have hfj : FinitePointJetBounded m f x l :=
          (FinitePointJetBounded.succ_of_fderiv hzero ih).mono_order (Nat.le_succ m)
        have hBfj : FinitePointJetBounded m (fun i y => B i (f i y)) x l :=
          hfj.comp (hBj m) hf hB
        have hinput := (hAj m).prodMk (hBfj.prodMk ih hBf hD) hA
          (fun i => (hBf i).prodMk (hD i))
        have hs : ∀ i, ContDiffAt ℝ ∞
            (fun y => (A i y, (B i (f i y), D i y))) (x i) :=
          fun i => (hA i).prodMk ((hBf i).prodMk (hD i))
        have hH := hinput.smooth_postcompose hs contDiff_transitionHessianPolynomial
        apply FinitePointJetBounded.succ_of_fderiv hfirst
        exact hH.congr (fun i => (hEq i).symm)
  intro m
  exact (FinitePointJetBounded.succ_of_fderiv hzero (hDj m)).mono_order (Nat.le_succ m)

end PoincareConjecture.M45
