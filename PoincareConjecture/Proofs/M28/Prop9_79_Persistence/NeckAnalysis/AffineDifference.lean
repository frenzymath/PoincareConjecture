import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.CovariantSmooth

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.Proofs.M28.NeckAnalysis

noncomputable def cylinderModelPlusDifference (u a : ℝ)
    (B C : RoundCylinderTwoTensor) : RoundCylinderTwoTensor :=
  fun z v w => EvolvingRoundCylinderMetric u z v w + a * (B z v w - C z v w)

theorem cylinderModelPlusDifference_coefficient (u a : ℝ)
    (B C : RoundCylinderTwoTensor)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (p : RoundCylinderCoordinates) (i j : Fin 3) :
    roundCylinderTensorCoefficient (cylinderModelPlusDifference u a B C) c p i j =
      roundCylinderGram u c p i j + a *
        (roundCylinderTensorCoefficient B c p i j - roundCylinderTensorCoefficient C c p i j) :=
  rfl

theorem cylinderModelPlusDifference_smooth {epsilon : ℝ} (u a : ℝ)
    {B C : RoundCylinderTwoTensor}
    (hB : RoundCylinderTensorSmoothOn epsilon B)
    (hC : RoundCylinderTensorSmoothOn epsilon C) :
    RoundCylinderTensorSmoothOn epsilon (cylinderModelPlusDifference u a B C) := by
  intro q i j
  simp_rw [cylinderModelPlusDifference_coefficient]
  have hscaled : ContDiffOn ℝ ∞ (fun p : RoundCylinderCoordinates =>
      a * (roundCylinderTensorCoefficient B
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j -
        roundCylinderTensorCoefficient C
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j))
      ((chartAt (EuclideanSpace ℝ (Fin 2)) q).target ×ˢ
        Ioo (-epsilon⁻¹) epsilon⁻¹) := by
    convert ContDiffOn.const_smul a ((hB q i j).sub (hC q i j)) using 1
    funext p
    simp [smul_eq_mul]
  exact (contDiff_roundCylinderGram u q i j).contDiffOn.add
    hscaled

theorem cylinderModelPlusDifference_error_zero (u a : ℝ)
    (B C : RoundCylinderTwoTensor)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (p : RoundCylinderCoordinates) (v : Fin 2 → Fin 3) :
    roundCylinderIteratedDerivative u c (cylinderModelPlusDifference u a B C) 0 p v =
      a * (roundCylinderTensorCoefficient B c p (v 0) (v 1) -
        roundCylinderTensorCoefficient C c p (v 0) (v 1)) := by
  change roundCylinderTensorCoefficient _ c p (v 0) (v 1) - _ = _
  rw [cylinderModelPlusDifference_coefficient]
  ring

theorem cylinderModelPlusDifference_iterated {epsilon u : ℝ} (hu : u < 1)
    (a : ℝ) {B C : RoundCylinderTwoTensor}
    (hB : RoundCylinderTensorSmoothOn epsilon B)
    (hC : RoundCylinderTensorSmoothOn epsilon C)
    (q : UnitTwoSphere) (k : ℕ)
    (p : RoundCylinderCoordinates)
    (hp : p ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) q).target ×ˢ
      Ioo (-epsilon⁻¹) epsilon⁻¹) :
    ∀ v, roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      (cylinderModelPlusDifference u a B C) k p v =
      a * (roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q) B k p v -
        roundCylinderIteratedDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q) C k p v) := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let S := c.target ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹
  have hS : IsOpen S := c.open_target.prod isOpen_Ioo
  induction k generalizing p with
  | zero =>
      intro v
      rw [cylinderModelPlusDifference_error_zero]
      change a * (_ - _) = a * ((_ - _) - (_ - _))
      ring
  | succ k ih =>
      intro v
      let tail : Fin (2 + k) → Fin 3 := fun b => v b.succ
      have heq : (fun y => roundCylinderIteratedDerivative u c
          (cylinderModelPlusDifference u a B C) k y tail) =ᶠ[𝓝 p]
          (fun y => a * (roundCylinderIteratedDerivative u c B k y tail -
            roundCylinderIteratedDerivative u c C k y tail)) := by
        filter_upwards [hS.mem_nhds hp] with y hy
        exact ih y hy tail
      have hb := (contDiffOn_roundCylinderIteratedDerivative hu hB q k tail).contDiffAt
        (hS.mem_nhds hp)
      have hc := (contDiffOn_roundCylinderIteratedDerivative hu hC q k tail).contDiffAt
        (hS.mem_nhds hp)
      have hd := ((hb.differentiableAt (by simp)).hasFDerivAt.sub
        (hc.differentiableAt (by simp)).hasFDerivAt).const_mul a
      have hlead : fderiv ℝ (fun y => roundCylinderIteratedDerivative u c
          (cylinderModelPlusDifference u a B C) k y tail) p (roundCylinderCoordinateBasis (v 0)) =
          a * (fderiv ℝ (fun y => roundCylinderIteratedDerivative u c B k y tail) p
            (roundCylinderCoordinateBasis (v 0)) -
          fderiv ℝ (fun y => roundCylinderIteratedDerivative u c C k y tail) p
            (roundCylinderCoordinateBasis (v 0))) := by
        have h := congrArg (fun L : RoundCylinderCoordinates →L[ℝ] ℝ =>
          L (roundCylinderCoordinateBasis (v 0))) (heq.fderiv_eq.trans hd.fderiv)
        exact h
      have hcorr : (∑ i : Fin (2 + k), ∑ j : Fin 3,
          roundCylinderChristoffel u c p j (v 0) (v i.succ) *
            roundCylinderIteratedDerivative u c (cylinderModelPlusDifference u a B C)
              k p (Function.update tail i j)) =
          a * ((∑ i : Fin (2 + k), ∑ j : Fin 3,
            roundCylinderChristoffel u c p j (v 0) (v i.succ) *
              roundCylinderIteratedDerivative u c B k p (Function.update tail i j)) -
            (∑ i : Fin (2 + k), ∑ j : Fin 3,
            roundCylinderChristoffel u c p j (v 0) (v i.succ) *
              roundCylinderIteratedDerivative u c C k p (Function.update tail i j))) := by
        simp only [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [ih p hp]
        ring
      change fderiv ℝ _ p _ - _ = a * ((fderiv ℝ _ p _ - _) - (fderiv ℝ _ p _ - _))
      dsimp [c] at hlead hcorr ⊢
      rw [hlead, hcorr]
      ring

end PoincareConjecture.Proofs.M28.NeckAnalysis
