import PoincareConjecture.Proofs.M47.CanonicalNeckAxialModel









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.Proofs.M47

local notation "E₂" => EuclideanSpace ℝ (Fin 2)


noncomputable def neckAxialTensorArray (lambda c : ℝ) {r : ℕ}
    (T : RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ) :
    RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ :=
  fun p a => (∏ i, neckAxialWeight lambda (a i)) * T (neckAxialCoordinate lambda c p) a



theorem roundCylinderTensorDerivative_neckAxialTensorArray
    (lambda c u : ℝ) (q : UnitTwoSphere) {r : ℕ}
    (T : RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ)
    (p : RoundCylinderCoordinates)
    (hT : ∀ a, DifferentiableAt ℝ (fun y => T y a) (neckAxialCoordinate lambda c p))
    (a : Fin (r + 1) → Fin 3) :
    roundCylinderTensorDerivative u (chartAt E₂ q) (neckAxialTensorArray lambda c T) p a =
      neckAxialTensorArray lambda c
        (roundCylinderTensorDerivative u (chartAt E₂ q) T) p a := by
  let tail : Fin r → Fin 3 := fun i => a i.succ
  have hd : fderiv ℝ (fun y => neckAxialTensorArray lambda c T y tail) p
      (roundCylinderCoordinateBasis (a 0)) =
      (∏ i, neckAxialWeight lambda (a i)) *
        fderiv ℝ (fun y => T y tail) (neckAxialCoordinate lambda c p)
          (roundCylinderCoordinateBasis (a 0)) := by
    have h := ((hT tail).hasFDerivAt.comp p
      (neckAxialCoordinate_hasFDerivAt lambda c p)).const_mul
        (∏ i, neckAxialWeight lambda (tail i))
    simp only [Function.comp_def] at h
    change fderiv ℝ (fun y => (∏ i, neckAxialWeight lambda (tail i)) *
        T (neckAxialCoordinate lambda c y) tail) p _ = _
    rw [h.fderiv]
    simp only [smul_apply, ContinuousLinearMap.comp_apply,
      neckAxialLinearMap_basis, map_smul, smul_eq_mul]
    rw [Fin.prod_univ_succ]
    dsimp only [tail]
    ring
  have hcorrection (i : Fin r) (j : Fin 3) :
      roundCylinderChristoffel u (chartAt E₂ q) p j (a 0) (a i.succ) *
          neckAxialTensorArray lambda c T p (Function.update tail i j) =
        (∏ k, neckAxialWeight lambda (a k)) *
          (roundCylinderChristoffel u (chartAt E₂ q) (neckAxialCoordinate lambda c p)
            j (a 0) (a i.succ) *
              T (neckAxialCoordinate lambda c p) (Function.update tail i j)) := by
    rw [roundCylinderChristoffel_neckAxialCoordinate]
    by_cases hzero : roundCylinderChristoffel u (chartAt E₂ q) p j (a 0) (a i.succ) = 0
    · rw [hzero]
      ring
    have hj : j ≠ 2 := fun h => hzero
      (roundCylinderChristoffel_axial_zero u q p j (a 0) (a i.succ) (Or.inl h))
    have h0 : a 0 ≠ 2 := fun h => hzero
      (roundCylinderChristoffel_axial_zero u q p j (a 0) (a i.succ) (Or.inr (Or.inl h)))
    have hi : a i.succ ≠ 2 := fun h => hzero
      (roundCylinderChristoffel_axial_zero u q p j (a 0) (a i.succ) (Or.inr (Or.inr h)))
    have hprod : (∏ k, neckAxialWeight lambda (Function.update tail i j k)) =
        ∏ k, neckAxialWeight lambda (tail k) := by
      apply Finset.prod_congr rfl
      intro k _
      by_cases hk : k = i
      · subst k
        simp [neckAxialWeight, tail, hj, hi]
      · rw [Function.update_of_ne hk]
    dsimp only [neckAxialTensorArray]
    rw [hprod, Fin.prod_univ_succ]
    simp only [neckAxialWeight, if_neg h0, one_mul]
    dsimp only [tail]
    ring
  change fderiv ℝ (fun y => neckAxialTensorArray lambda c T y tail) p
        (roundCylinderCoordinateBasis (a 0)) -
      ∑ i : Fin r, ∑ j : Fin 3,
        roundCylinderChristoffel u (chartAt E₂ q) p j (a 0) (a i.succ) *
          neckAxialTensorArray lambda c T p (Function.update tail i j) =
    (∏ i, neckAxialWeight lambda (a i)) *
      (fderiv ℝ (fun y => T y tail) (neckAxialCoordinate lambda c p)
          (roundCylinderCoordinateBasis (a 0)) -
        ∑ i : Fin r, ∑ j : Fin 3,
          roundCylinderChristoffel u (chartAt E₂ q) (neckAxialCoordinate lambda c p)
              j (a 0) (a i.succ) *
            T (neckAxialCoordinate lambda c p) (Function.update tail i j))
  rw [hd, mul_sub]
  simp_rw [Finset.mul_sum, hcorrection]

end PoincareConjecture.Proofs.M47
