import PoincareConjecture.Proofs.M47.BlowupControlsCapNativeScaling










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M47

open Proofs.M47

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "V" => RoundCylinderCoordinates



theorem cap_native_axial_normalized_zero
    (beta lambda c u : ℝ) (hscale : beta * lambda ^ 2 = 1)
    (B : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ)
    (q : UnitTwoSphere) (p : V) (a : Fin 2 → Fin 3) :
    roundCylinderIteratedDerivative u (chartAt E2 q)
        (fun z v w => beta * neckAxialTensorPullback lambda c
          (fun z v w => B z v w) z v w) 0 p a =
      beta * neckAxialTensorArray lambda c
        (roundCylinderIteratedDerivative u (chartAt E2 q) (fun z v w => B z v w) 0) p a +
      (beta - 1) * (roundCylinderGram u (chartAt E2 q) p (a 0) (a 1) -
        neckAxialConstantArray 1 a) := by
  have h := roundCylinderIteratedDerivative_neckAxialTensorPullback_zero lambda c u B q p a
  have hscaled : roundCylinderIteratedDerivative u (chartAt E2 q)
        (fun z v w => beta * neckAxialTensorPullback lambda c
          (fun z v w => B z v w) z v w) 0 p a =
      beta * roundCylinderIteratedDerivative u (chartAt E2 q)
        (neckAxialTensorPullback lambda c (fun z v w => B z v w)) 0 p a +
      (beta - 1) * roundCylinderGram u (chartAt E2 q) p (a 0) (a 1) := by
    simp only [roundCylinderIteratedDerivative, roundCylinderTensorCoefficient]
    ring
  rw [hscaled, h]
  simp only [neckAxialConstantArray, Fin.forall_fin_two, one_mul]
  by_cases hax : a 0 = 2 ∧ a 1 = 2
  · simp only [if_pos hax]
    nlinarith only [hscale]
  · simp only [if_neg hax, mul_zero, add_zero, sub_zero]



theorem cap_native_axial_normalized_succ
    (beta lambda c : ℝ) {u : ℝ} (hu : u < 1)
    (B : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ)
    (q : UnitTwoSphere) {U : Set V} (hU : IsOpen U)
    (hB : ∀ i j : Fin 3, ContDiffOn ℝ ∞
      (fun y => roundCylinderTensorCoefficient (fun z v w => B z v w) (chartAt E2 q) y i j) U)
    (k : ℕ) (p : V) (hp : neckAxialCoordinate lambda c p ∈ U)
    (a : Fin (2 + (k + 1)) → Fin 3) :
    roundCylinderIteratedDerivative u (chartAt E2 q)
        (fun z v w => beta * neckAxialTensorPullback lambda c
          (fun z v w => B z v w) z v w) (k + 1) p a =
      beta * neckAxialTensorArray lambda c
        (roundCylinderIteratedDerivative u (chartAt E2 q)
          (fun z v w => B z v w) (k + 1)) p a := by
  let Bs : RoundCylinderSpace → V →L[ℝ] V →L[ℝ] ℝ := fun z => beta • B z
  have hBs (i j : Fin 3) : ContDiffOn ℝ ∞
      (fun y => roundCylinderTensorCoefficient (fun z v w => Bs z v w)
        (chartAt E2 q) y i j) U := by
    simpa only [Bs, roundCylinderTensorCoefficient, smul_apply, smul_eq_mul] using
      (contDiffOn_const.mul (hB i j) : ContDiffOn ℝ ∞
        (fun y => beta * roundCylinderTensorCoefficient (fun z v w => B z v w)
          (chartAt E2 q) y i j) U)
  have h := roundCylinderIteratedDerivative_neckAxialTensorPullback_succ lambda c hu Bs q
    hU hBs k p hp a
  change roundCylinderIteratedDerivative u (chartAt E2 q)
      (fun z v w => beta * neckAxialTensorPullback lambda c
        (fun z v w => B z v w) z v w) (k + 1) p a =
    neckAxialTensorArray lambda c
      (roundCylinderIteratedDerivative u (chartAt E2 q)
        (fun z v w => beta * B z v w) (k + 1)) p a at h
  rw [h]
  unfold neckAxialTensorArray
  rw [cap_native_iterated_scalar_mul_succ beta u hu (fun z v w => B z v w) q
    hU hB k _ hp a]
  ring

end PoincareConjecture.M47
