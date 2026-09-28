import PoincareConjecture.Proofs.M35.Thm12_28.CylinderChristoffel










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.M35



theorem fderiv_roundCylinderTensorDerivative_center {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) (s : ℝ) {r : ℕ}
    (T : RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ)
    (hT : ∀ a, ContDiffAt ℝ ∞ (fun p => T p a) (0, s))
    (a : Fin (r + 1) → Fin 3) (v : RoundCylinderCoordinates) :
    fderiv ℝ (fun p => roundCylinderTensorDerivative u
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) T p a) (0, s) v =
      fderiv ℝ (fun p => fderiv ℝ (fun x => T x (fun i => a i.succ)) p
        (roundCylinderCoordinateBasis (a 0))) (0, s) v -
      ∑ i : Fin r, ∑ j : Fin 3,
        fderiv ℝ (fun p => roundCylinderChristoffel u
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) p j (a 0) (a i.succ)) (0, s) v *
          T (0, s) (Function.update (fun k => a k.succ) i j) := by
  classical
  have hfirst := (((hT (fun i => a i.succ)).fderiv_right (m := ∞)
    (by simp)).clm_apply (contDiffAt_const
      (c := roundCylinderCoordinateBasis (a 0)))).differentiableAt (by simp)
  have hc (i : Fin r) (j : Fin 3) :=
    ((contDiff_roundCylinderChristoffel hu q j (a 0) (a i.succ)).differentiable
      (by simp) (0, s)).hasFDerivAt.mul
        ((hT (Function.update (fun k => a k.succ) i j)).differentiableAt
          (by simp)).hasFDerivAt
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hc i j))
  have hd := hfirst.hasFDerivAt.sub hs
  unfold roundCylinderTensorDerivative
  convert! congrArg (fun L : RoundCylinderCoordinates →L[ℝ] ℝ => L v) hd.fderiv using 1
  simp [roundCylinderChristoffel_center, mul_comm]



theorem roundCylinderIteratedDerivative_two_center {u : ℝ} (hu : u < 1)
    (q : UnitTwoSphere) (s : ℝ) (B : RoundCylinderTwoTensor)
    (hB : ∀ a b, ContDiffAt ℝ ∞ (fun p : RoundCylinderCoordinates =>
      roundCylinderTensorCoefficient B (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b)
        (0, s)) (a : Fin 4 → Fin 3) :
    roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      B 2 (0, s) a =
      fderiv ℝ (fun p => fderiv ℝ (fun x => roundCylinderIteratedDerivative u
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) B 0 x
          (fun i : Fin 2 => a i.succ.succ)) p (roundCylinderCoordinateBasis (a 1)))
        (0, s) (roundCylinderCoordinateBasis (a 0)) -
      ∑ i : Fin 2, ∑ j : Fin 3,
        fderiv ℝ (fun p => roundCylinderChristoffel u
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) p j (a 1) (a i.succ.succ))
          (0, s) (roundCylinderCoordinateBasis (a 0)) *
        roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
          B 0 (0, s) (Function.update (fun k : Fin 2 => a k.succ.succ) i j) := by
  have hT (b : Fin 2 → Fin 3) : ContDiffAt ℝ ∞ (fun p =>
      roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        B 0 p b) (0, s) :=
    (hB (b 0) (b 1)).sub (contDiff_roundCylinderGram u q (b 0) (b 1)).contDiffAt
  change roundCylinderTensorDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
    (roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q) B 1)
    (0, s) a = _
  rw [roundCylinderTensorDerivative_center]
  exact fderiv_roundCylinderTensorDerivative_center hu q s _ hT
    (fun i : Fin 3 => a i.succ) (roundCylinderCoordinateBasis (a 0))

end PoincareConjecture.M35
