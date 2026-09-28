import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckComparison
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Logic.Equiv.Fin.Basic











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)




theorem roundCylinderGram_chosenChart (u : ℝ) (q : UnitTwoSphere)
    (p : RoundCylinderCoordinates) :
    roundCylinderGram u (chartAt E₂ q) p = Matrix.diagonal
      ![2 * (1 - u) * (16 / (‖p.1‖ ^ 2 + 4) ^ 2),
        2 * (1 - u) * (16 / (‖p.1‖ ^ 2 + 4) ^ 2), 1] := by
  let : Fact (Module.finrank ℝ E₃ = 2 + 1) := ⟨by simp⟩
  ext i j
  change 2 * (1 - u) * inner ℝ (E := E₃)
      (mfderiv (𝓡 2) (𝓡 3) (fun z : UnitTwoSphere => (z : E₃))
        ((chartAt E₂ q).symm p.1)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ q).symm p.1
          (roundCylinderCoordinateBasis i).1))
      (mfderiv (𝓡 2) (𝓡 3) (fun z : UnitTwoSphere => (z : E₃))
        ((chartAt E₂ q).symm p.1)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ q).symm p.1
          (roundCylinderCoordinateBasis j).1)) +
      (roundCylinderCoordinateBasis i).2 * (roundCylinderCoordinateBasis j).2 = _
  rw [inner_mfderiv_sphere_chart_symm]
  fin_cases i <;> fin_cases j <;>
    simp [roundCylinderCoordinateBasis, Matrix.diagonal,
      EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left]



theorem mfderiv_sphere_chart_symm_center (q : UnitTwoSphere) :
    mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ q).symm (chartAt E₂ q q) =
      ContinuousLinearMap.id ℝ E₂ := by
  have h := mfderivWithin_range_extChartAt_symm (I := 𝓡 2) (x := q)
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at h
  convert! h using 1



theorem roundCylinderTensorCoefficient_chart_center
    (B : RoundCylinderTwoTensor) (z : RoundCylinderSpace) (a b : Fin 3) :
    roundCylinderTensorCoefficient B (chartAt E₂ z.1) (chartAt E₂ z.1 z.1, z.2) a b =
      B z (roundCylinderCoordinateBasis a) (roundCylinderCoordinateBasis b) := by
  have hz := (chartAt E₂ z.1).left_inv (mem_chart_source E₂ z.1)
  simp only [roundCylinderTensorCoefficient, mfderiv_sphere_chart_symm_center]
  change B ((chartAt E₂ z.1).symm (chartAt E₂ z.1 z.1), z.2)
    (roundCylinderCoordinateBasis a) (roundCylinderCoordinateBasis b) = _
  rw [hz]



theorem roundCylinderJetErrorSquared_zero_eq
    (B : RoundCylinderTwoTensor) (z : RoundCylinderSpace) :
    roundCylinderJetErrorSquared 0 B 0 z =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (![2, 2, 1] i : ℝ)⁻¹ * (![2, 2, 1] j : ℝ)⁻¹ *
          (B z (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j) -
            EvolvingRoundCylinderMetric 0 z
              (roundCylinderCoordinateBasis i) (roundCylinderCoordinateBasis j)) ^ 2 := by
  simp only [roundCylinderJetErrorSquared, Nat.zero_add, Finset.range_one, Finset.sum_singleton]
  unfold roundCylinderTensorNormSquared
  rw [roundCylinderGram_chart_center_inv (by norm_num : (0 : ℝ) ≠ 1)]
  have hvec : (![(2 * (1 - (0 : ℝ)))⁻¹, (2 * (1 - (0 : ℝ)))⁻¹, 1] : Fin 3 → ℝ) =
      fun i => (![2, 2, 1] i : ℝ)⁻¹ := by
    ext i
    fin_cases i <;> norm_num
  rw [hvec, diagonal_tensor_contraction (ι := Fin 2) (κ := Fin 3)]
  simp only [Fin.prod_univ_two, roundCylinderIteratedDerivative,
    roundCylinderGram, roundCylinderTensorCoefficient_chart_center]
  exact ((finTwoArrowEquiv (Fin 3)).sum_comp (fun p : Fin 3 × Fin 3 =>
    (![2, 2, 1] p.1 : ℝ)⁻¹ * (![2, 2, 1] p.2 : ℝ)⁻¹ *
      (B z (roundCylinderCoordinateBasis p.1) (roundCylinderCoordinateBasis p.2) -
        EvolvingRoundCylinderMetric 0 z
          (roundCylinderCoordinateBasis p.1) (roundCylinderCoordinateBasis p.2)) ^ 2)).trans
    (Fintype.sum_prod_type _)



theorem sum_roundCylinderCoordinateBasis (v : RoundCylinderCoordinates) :
    (∑ i : Fin 3, (![v.1 0, v.1 1, v.2] i : ℝ) • roundCylinderCoordinateBasis i) = v := by
  apply Prod.ext
  · apply PiLp.ext
    intro i
    fin_cases i <;> simp [Fin.sum_univ_succ, roundCylinderCoordinateBasis,
      EuclideanSpace.basisFun_apply]
  · simp [Fin.sum_univ_succ, roundCylinderCoordinateBasis]

end PoincareConjecture.M34
