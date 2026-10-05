import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Blowup.Cylinder.Curvature.CylinderChristoffel

/-!
# Second jets in the literal cylinder comparison

Morgan-Tian Definition 2.16, p. 30, used in Theorem 12.28, pp. 323-324.
At a preferred chart center the second covariant derivative differs from
the ordinary second derivative by the model connection derivative times
the zeroth tensor. This correction is retained in every covariant slot.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareMT.M35

/-- Definition 2.16, p. 30: differentiating the actual covariant recursion
at the chart center retains the connection-derivative correction in each slot. -/
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

/-- Definition 2.16, p. 30: the second metric-error jet in the frozen
recursion is its ordinary second jet minus the exact model connection correction. -/
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

end PoincareMT.M35
