import PoincareConjecture.Proofs.M25.AppA_1_Necks.RoundCylinderReflection
import Mathlib.Algebra.BigOperators.Fin










set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture


noncomputable def roundCylinderSlotSign {r : ℕ} (a : Fin r → Fin 3) : ℝ :=
  ∏ i, roundCylinderAxialSign (a i)



theorem roundCylinderSlotSign_mul_self {r : ℕ} (a : Fin r → Fin 3) :
    roundCylinderSlotSign a * roundCylinderSlotSign a = 1 := by
  unfold roundCylinderSlotSign
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro i _
  by_cases h : a i = 2 <;> simp [roundCylinderAxialSign, h]



theorem roundCylinderSlotSign_succ {r : ℕ} (a : Fin (r + 1) → Fin 3) :
    roundCylinderSlotSign a =
      roundCylinderAxialSign (a 0) *
        roundCylinderSlotSign (fun i : Fin r => a i.succ) :=
  Fin.prod_univ_succ _



theorem roundCylinderSlotSign_update {r : ℕ}
    (a : Fin r → Fin 3) (i : Fin r) (j : Fin 3) :
    roundCylinderSlotSign (Function.update a i j) =
      roundCylinderSlotSign a *
        roundCylinderAxialSign (a i) * roundCylinderAxialSign j := by
  classical
  let P := ∏ k ∈ Finset.univ.erase i, roundCylinderAxialSign (a k)
  have hold : roundCylinderSlotSign a = roundCylinderAxialSign (a i) * P :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hnew : roundCylinderSlotSign (Function.update a i j) =
      roundCylinderAxialSign j * P := by
    unfold roundCylinderSlotSign
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]
  rw [hnew, hold]
  by_cases h : a i = 2 <;> simp [roundCylinderAxialSign, h]



noncomputable def roundCylinderTensorReflection {r : ℕ}
    (T : RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ)
    (p : RoundCylinderCoordinates) (a : Fin r → Fin 3) : ℝ :=
  roundCylinderSlotSign a * T (roundCylinderCoordinateReflection p) a



theorem roundCylinderTensorDerivative_axialReflection
    (q : UnitTwoSphere) {r : ℕ}
    (T : RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ)
    (p : RoundCylinderCoordinates) (a : Fin (r + 1) → Fin 3) :
    roundCylinderTensorDerivative 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (roundCylinderTensorReflection T) p a =
      roundCylinderSlotSign a *
        roundCylinderTensorDerivative 0
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) T
          (roundCylinderCoordinateReflection p) a := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let J := roundCylinderCoordinateReflection
  let σ := roundCylinderAxialSign
  let b : Fin r → Fin 3 := fun i => a i.succ
  have hσ (j : Fin 3) : σ j * σ j = 1 := by
    by_cases hj : j = 2 <;> simp [σ, roundCylinderAxialSign, hj]
  have hterm (i : Fin r) (j : Fin 3) :
      roundCylinderChristoffel 0 c p j (a 0) (b i) *
          (roundCylinderSlotSign (Function.update b i j) *
            T (J p) (Function.update b i j)) =
        roundCylinderSlotSign b * σ (a 0) *
          (roundCylinderChristoffel 0 c (J p) j (a 0) (b i) *
            T (J p) (Function.update b i j)) := by
    rw [roundCylinderChristoffel_axialReflection q p,
      roundCylinderSlotSign_update]
    change (σ j * σ (a 0) * σ (b i) *
        roundCylinderChristoffel 0 c (J p) j (a 0) (b i)) *
        (roundCylinderSlotSign b * σ (b i) * σ j *
          T (J p) (Function.update b i j)) = _
    calc
      _ = (σ (b i) * σ (b i)) * (σ j * σ j) *
          (roundCylinderSlotSign b * σ (a 0) *
            (roundCylinderChristoffel 0 c (J p) j (a 0) (b i) *
              T (J p) (Function.update b i j))) := by ring
      _ = _ := by rw [hσ, hσ]; simp
  unfold roundCylinderTensorDerivative
  simp only [roundCylinderTensorReflection]
  rw [roundCylinderCoordinateReflection_fderiv_apply
    (fun x => T x b) (roundCylinderSlotSign b) p (a 0)]
  dsimp only [c, J, σ, b] at hterm
  simp_rw [hterm, ← Finset.mul_sum]
  rw [roundCylinderSlotSign_succ]
  ring



theorem roundCylinderTensorNormSquared_axialReflection
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) {r : ℕ}
    (T : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) p
        (fun a => roundCylinderSlotSign a * T a) =
      roundCylinderTensorNormSquared 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (roundCylinderCoordinateReflection p) T := by
  unfold roundCylinderTensorNormSquared
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hprod :
      (∏ i : Fin r,
        (roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) p)⁻¹
          (a i) (b i)) =
        roundCylinderSlotSign a * roundCylinderSlotSign b *
          ∏ i : Fin r,
            (roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
              (roundCylinderCoordinateReflection p))⁻¹ (a i) (b i) := by
    simp only [roundCylinderSlotSign, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    exact roundCylinderGram_inv_axialReflection q p (a i) (b i)
  rw [hprod]
  calc
    _ = (roundCylinderSlotSign a * roundCylinderSlotSign a) *
        (roundCylinderSlotSign b * roundCylinderSlotSign b) *
        ((∏ i : Fin r,
            (roundCylinderGram 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
              (roundCylinderCoordinateReflection p))⁻¹ (a i) (b i)) * T a * T b) := by
      ring
    _ = _ := by
      rw [roundCylinderSlotSign_mul_self, roundCylinderSlotSign_mul_self]
      simp

end PoincareConjecture
