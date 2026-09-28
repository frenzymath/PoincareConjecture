import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceScalarContinuity
import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.StereographicCurvature











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

local notation "E₃" => EuclideanSpace ℝ (Fin 3)



theorem capPersistence_stereographic_scalar_origin
    (D : LeviCivitaData (stereographicCylinderMetric 2 (by norm_num))) :
    D.scalarCurvature 0 = 1 := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have hb (i j : Fin 3) : (b i) j = if i = j then 1 else 0 := by
    change (EuclideanSpace.basisFun (Fin 3) ℝ i) j = _
    simp [EuclideanSpace.basisFun_apply, PiLp.single_apply, eq_comm]
  have hgram : Matrix.of (fun i j => stereographicCylinderCoefficients 2 0 (b i) (b j)) =
        Matrix.diagonal ![2, 2, 1] := by
    ext i j
    change stereographicCylinderCoefficients 2 0 (b i) (b j) = _
    rw [stereographicCylinderCoefficients_apply]
    simp only [hb]
    fin_cases i <;> fin_cases j <;>
      norm_num [stereographicCylinderDensity, stereographicCylinderDenominator,
        Matrix.diagonal, Fin.ext_iff]
  have hricci (i j : Fin 3) : D.ricci 0 (b i) (b j) =
      Matrix.diagonal (![1, 1, 0] : Fin 3 → ℝ) i j := by
    rw [stereographicCylinderRicci (by norm_num) D]
    simp only [hb]
    fin_cases i <;> fin_cases j <;>
      norm_num [stereographicCylinderDensity, stereographicCylinderDenominator,
        Matrix.diagonal, Fin.ext_iff]
  have hscalar : D.scalarCurvature 0 = ∑ i : Fin 3, ∑ j : Fin 3,
      (Matrix.of (fun i j => stereographicCylinderCoefficients 2 0 (b i) (b j)))⁻¹ i j *
        D.ricci 0 (b i) (b j) := by
    convert! D.scalarCurvature_eq_inverse_gram 0 b using 1
  have hi : (Matrix.diagonal (![2, 2, 1] : Fin 3 → ℝ))⁻¹ =
      Matrix.diagonal ![1 / 2, 1 / 2, 1] := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal, Fin.ext_iff]
  rw [hscalar, hgram, hi]
  simp only [hricci]
  simp only [Matrix.diagonal_apply, ite_mul, zero_mul]
  norm_num [Fin.sum_univ_three,
    show (![1, 1, 0] : Fin 3 → ℝ) 2 = 0 from rfl]



theorem capPersistence_exists_scalar_one_tolerance {eta : ℝ} (heta : 0 < eta) :
    ∃ zeta : ℝ, 0 < zeta ∧ ∀ (g : RiemannianMetric 3 E₃) (D : LeviCivitaData g),
      (∀ j ≤ 2, ∀ a b : Fin 3, ‖iteratedFDeriv ℝ j (fun y =>
        g.euclideanCoefficients y (EuclideanSpace.basisFun (Fin 3) ℝ a)
            (EuclideanSpace.basisFun (Fin 3) ℝ b) -
          stereographicCylinderCoefficients 2 y (EuclideanSpace.basisFun (Fin 3) ℝ a)
            (EuclideanSpace.basisFun (Fin 3) ℝ b)) 0‖ ≤ zeta) →
        |D.scalarCurvature 0 - 1| < eta := by
  let g₀ := stereographicCylinderMetric 2 (by norm_num)
  let D₀ := g₀.euclideanLeviCivitaData
  obtain ⟨zeta, hzeta, hbound⟩ := capPersistence_exists_scalar_tolerance D₀ 0 heta
  refine ⟨zeta, hzeta, ?_⟩
  intro g D hb
  have h := hbound g D hb
  rwa [capPersistence_stereographic_scalar_origin D₀] at h

end PoincareConjecture.M34
