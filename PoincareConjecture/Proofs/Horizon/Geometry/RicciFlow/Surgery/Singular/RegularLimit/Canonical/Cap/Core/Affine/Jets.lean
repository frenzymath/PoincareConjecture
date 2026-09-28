import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Affine.Model
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Affine.Translation
import Mathlib.Analysis.Calculus.FDeriv.Equiv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.RoundCylinderAffine

noncomputable def linear (a : ℝ) (ha : a ≠ 0) :
    RoundCylinderCoordinates ≃L[ℝ] RoundCylinderCoordinates :=
  (ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin 2))).prodCongr
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := ℝ) (Units.mk0 a ha))

def coordinates (a s : ℝ) (p : RoundCylinderCoordinates) : RoundCylinderCoordinates :=
  (p.1, a * p.2 + s)

def axisWeight (a : ℝ) (i : Fin 3) : ℝ := if i = 2 then a else 1

def tensorWeight (a : ℝ) {r : ℕ} (i : Fin r → Fin 3) : ℝ := ∏ k, axisWeight a (i k)

theorem linear_apply (a : ℝ) (ha : a ≠ 0) (p : RoundCylinderCoordinates) :
    linear a ha p = (p.1, a * p.2) := rfl

theorem coordinates_eq_linear_add (a s : ℝ) (ha : a ≠ 0) (p : RoundCylinderCoordinates) :
    coordinates a s p = linear a ha p + (0, s) := by
  apply Prod.ext <;> simp [coordinates, linear_apply]

theorem linear_basis (a : ℝ) (ha : a ≠ 0) (i : Fin 3) :
    linear a ha (roundCylinderCoordinateBasis i) =
      axisWeight a i • roundCylinderCoordinateBasis i := by
  fin_cases i <;> simp [linear_apply, roundCylinderCoordinateBasis, axisWeight]

theorem fderiv_affine (a s : ℝ) (ha : a ≠ 0)
    (f : RoundCylinderCoordinates → ℝ) (p : RoundCylinderCoordinates) (i : Fin 3) :
    fderiv ℝ (fun q => f (coordinates a s q)) p (roundCylinderCoordinateBasis i) =
      axisWeight a i * fderiv ℝ f (coordinates a s p) (roundCylinderCoordinateBasis i) := by
  simp only [coordinates_eq_linear_add a s ha]
  change fderiv ℝ ((fun q => f (q + (0, s))) ∘ linear a ha) p _ = _
  rw [(linear a ha).comp_right_fderiv, fderiv_comp_add_right]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    linear_basis, map_smul, smul_eq_mul]

theorem coefficient_pullback (a s : ℝ) (B : RoundCylinderTwoTensor)
    (hB : ∀ (z : RoundCylinderSpace) (c d : ℝ) (v w : RoundCylinderTangent z),
      B z (c • v) (d • w) = c * d * B z v w)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) (i j : Fin 3) :
    roundCylinderTensorCoefficient (pullback a s B)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j =
      axisWeight a i * axisWeight a j * roundCylinderTensorCoefficient B
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) (coordinates a s p) i j := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  have hv (i : Fin 3) :
      (mfderiv (𝓡 2) (𝓡 2) c.symm p.1 (roundCylinderCoordinateBasis i).1,
        a * (roundCylinderCoordinateBasis i).2) =
      axisWeight a i • (mfderiv (𝓡 2) (𝓡 2) c.symm p.1
        (roundCylinderCoordinateBasis i).1, (roundCylinderCoordinateBasis i).2) := by
    fin_cases i <;> simp [roundCylinderCoordinateBasis, axisWeight]
  unfold roundCylinderTensorCoefficient pullback
  dsimp only [space, coordinates]
  rw [hv i, hv j, hB]

theorem tensorWeight_nonneg {a : ℝ} (ha : 0 ≤ a) {r : ℕ} (i : Fin r → Fin 3) :
    0 ≤ tensorWeight a i := by
  apply Finset.prod_nonneg
  intro k _
  simp only [axisWeight]
  split <;> positivity

theorem tensorWeight_le_one {a : ℝ} (ha : 0 ≤ a) (haone : a ≤ 1)
    {r : ℕ} (i : Fin r → Fin 3) : tensorWeight a i ≤ 1 := by
  apply Finset.prod_le_one
  · intro k _
    simp only [axisWeight]
    split <;> positivity
  · intro k _
    simp only [axisWeight]
    split <;> linarith

theorem tensorNorm_contraction {a u : ℝ} (ha : 0 ≤ a) (haone : a ≤ 1) (hu : u < 1)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) {r : ℕ}
    (A : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p
        (fun i => tensorWeight a i * A i) ≤
      roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p A := by
  rw [SingularRegularLimit.cylinderNorm_diagonal hu.ne,
    SingularRegularLimit.cylinderNorm_diagonal hu.ne]
  apply Finset.sum_le_sum
  intro i _
  have hw := tensorWeight_nonneg ha i
  have hwone := tensorWeight_le_one ha haone i
  have hsq : (tensorWeight a i * A i) ^ 2 ≤ (A i) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right
      (show (tensorWeight a i) ^ 2 ≤ 1 by nlinarith) (sq_nonneg (A i))
    nlinarith
  exact mul_le_mul_of_nonneg_left hsq (Finset.prod_nonneg
    (fun k _ => (SingularRegularLimit.cylinderWeight_pos hu p (i k)).le))

theorem christoffel_affine (a s u : ℝ) (q : UnitTwoSphere) (p : RoundCylinderCoordinates)
    (i j k : Fin 3) :
    roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (coordinates a s p) i j k =
      roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j k := by
  have heq : coordinates a s p =
      RoundCylinderTranslation.coordinates (a * p.2 + s - p.2) p := by
    apply Prod.ext
    · rfl
    · dsimp only [coordinates, RoundCylinderTranslation.coordinates]
      ring
  rw [heq, RoundCylinderTranslation.christoffel_translate]

theorem christoffel_eq_zero_of_axial {u : ℝ} (hu : u ≠ 1)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) (i j k : Fin 3)
    (haxis : i = 2 ∨ j = 2 ∨ k = 2) :
    roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p i j k = 0 := by
  rw [SingularRegularLimit.roundCylinderChristoffel_time_eq hu]
  simp only [roundCylinderChristoffel, SingularRegularLimit.cylinderGram_fderiv]
  rw [SingularRegularLimit.cylinderGram_inv_diagonal (by norm_num : (0 : ℝ) ≠ 1)]
  rcases haxis with rfl | rfl | rfl
  · fin_cases j <;> fin_cases k <;>
      simp [Matrix.diagonal, SingularRegularLimit.cylinderWeight,
        roundCylinderCoordinateBasis, EuclideanSpace.inner_single_left,
        SingularRegularLimit.sphereFactor_fderiv_axis]
  · fin_cases i <;> fin_cases k <;>
      simp [Matrix.diagonal, SingularRegularLimit.cylinderWeight,
        roundCylinderCoordinateBasis, EuclideanSpace.inner_single_left,
        SingularRegularLimit.sphereFactor_fderiv_axis]
  · fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal, SingularRegularLimit.cylinderWeight,
        roundCylinderCoordinateBasis, EuclideanSpace.inner_single_left,
        SingularRegularLimit.sphereFactor_fderiv_axis]

theorem tensorWeight_succ (a : ℝ) {r : ℕ} (i : Fin (r + 1) → Fin 3) :
    tensorWeight a i = axisWeight a (i 0) * tensorWeight a (fun k => i k.succ) :=
  Fin.prod_univ_succ _

theorem christoffel_weight_update (a s : ℝ) {u : ℝ} (hu : u ≠ 1)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) {r : ℕ}
    (i : Fin (r + 1) → Fin 3) (k : Fin r) (j : Fin 3) :
    roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p j (i 0) (i k.succ) *
        tensorWeight a (Function.update (fun l => i l.succ) k j) =
      tensorWeight a i * roundCylinderChristoffel u
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) (coordinates a s p) j (i 0) (i k.succ) := by
  rw [christoffel_affine]
  by_cases haxis : j = 2 ∨ i 0 = 2 ∨ i k.succ = 2
  · rw [christoffel_eq_zero_of_axial hu q p _ _ _ haxis]
    simp
  · have hj : j ≠ 2 := fun h => haxis (Or.inl h)
    have hzero : i 0 ≠ 2 := fun h => haxis (Or.inr (Or.inl h))
    have hk : i k.succ ≠ 2 := fun h => haxis (Or.inr (Or.inr h))
    have hw : tensorWeight a (Function.update (fun l => i l.succ) k j) =
        tensorWeight a (fun l => i l.succ) := by
      apply Finset.prod_congr rfl
      intro l _
      by_cases hl : l = k
      · subst l
        simp [axisWeight, hj, hk]
      · simp [Function.update_of_ne hl]
    rw [hw, tensorWeight_succ, axisWeight, if_neg hzero, one_mul, mul_comm]

noncomputable def tensorPullback (a s : ℝ) {r : ℕ}
    (A : RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ) :
    RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ :=
  fun p i => tensorWeight a i * A (coordinates a s p) i

theorem derivative_tensorPullback (a s : ℝ) (ha : a ≠ 0) {u : ℝ} (hu : u ≠ 1)
    (q : UnitTwoSphere) {r : ℕ}
    (A : RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ)
    (p : RoundCylinderCoordinates) (i : Fin (r + 1) → Fin 3) :
    roundCylinderTensorDerivative u (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (tensorPullback a s A) p i =
      tensorWeight a i * roundCylinderTensorDerivative u
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) A (coordinates a s p) i := by
  have hd : fderiv ℝ (fun p => tensorWeight a (fun k => i k.succ) *
        A (coordinates a s p) (fun k => i k.succ)) p (roundCylinderCoordinateBasis (i 0)) =
      tensorWeight a i * fderiv ℝ (fun p => A p (fun k => i k.succ))
        (coordinates a s p) (roundCylinderCoordinateBasis (i 0)) := by
    change fderiv ℝ (tensorWeight a (fun k => i k.succ) •
      (fun p => A (coordinates a s p) (fun k => i k.succ))) p _ = _
    rw [fderiv_const_smul_field]
    simp only [Pi.smul_apply, smul_apply, smul_eq_mul]
    rw [fderiv_affine a s ha (fun p => A p (fun k => i k.succ)) p (i 0),
      tensorWeight_succ]
    ring
  unfold roundCylinderTensorDerivative tensorPullback
  rw [hd, mul_sub]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc, christoffel_weight_update a s hu q p i k j]
  ring

end PoincareConjecture.RoundCylinderAffine
