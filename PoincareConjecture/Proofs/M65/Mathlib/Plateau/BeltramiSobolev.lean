import PoincareConjecture.Proofs.M65.Mathlib.Plateau.BeltramiDerivativeBounds
import PoincareConjecture.Proofs.M03.Existence.EuclideanFourierCoordinatesNative

set_option autoImplicit false

noncomputable section

open MeasureTheory FourierTransform Filter LineDeriv
open scoped Topology SchwartzMap ContDiff ComplexConjugate LineDeriv

namespace Complex

open PoincareConjecture.EuclideanFourierCoordinatesNative
open PoincareConjecture.EuclideanSobolevContinuousNative

private def euclideanPullback (h : 𝓢(ℂ, ℂ)) : 𝓢(EuclideanSpace ℝ (Fin 2), ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv h

private theorem norm_toLp_euclideanPullback (h : 𝓢(ℂ, ℂ)) :
    ‖(euclideanPullback h).toLp 2 volume‖ = ‖h.toLp 2 volume‖ := by
  rw [SchwartzMap.norm_toLp, SchwartzMap.norm_toLp]
  congr 1
  exact eLpNorm_comp_measurePreserving h.continuous.aestronglyMeasurable
    orthonormalBasisOneI.measurePreserving_repr_symm

private theorem lineDeriv_euclideanPullback (h : 𝓢(ℂ, ℂ)) (i : Fin 2) :
    ∂_{EuclideanSpace.single i (1 : ℝ)} (euclideanPullback h) =
      euclideanPullback (∂_{orthonormalBasisOneI i} h) := by
  unfold euclideanPullback
  rw [SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv]
  congr 2
  exact orthonormalBasisOneI.repr_symm_single i

private theorem coordinateSecond_euclideanPullback (h : 𝓢(ℂ, ℂ)) (i : Fin 2) :
    coordinateSecond i (euclideanPullback h) =
      euclideanPullback (∂_{orthonormalBasisOneI i} (∂_{orthonormalBasisOneI i} h)) := by
  simp only [coordinateSecond, lineDeriv_euclideanPullback]

private theorem budget_second_le (m : ℕ) (h : 𝓢(ℂ, ℂ)) (i : Fin 2) :
    planeDerivativeL2Budget (2 * m)
      (∂_{orthonormalBasisOneI i} (∂_{orthonormalBasisOneI i} h)) ≤
        planeDerivativeL2Budget (2 * (m + 1)) h := by
  calc
    _ ≤ planeDerivativeL2Budget (2 * m + 1) (∂_{orthonormalBasisOneI i} h) :=
      planeDerivativeL2Budget_coordinate_le _ _ i
    _ ≤ planeDerivativeL2Budget (2 * m + 1 + 1) h :=
      planeDerivativeL2Budget_coordinate_le _ _ i
    _ = _ := by congr 1

private theorem exists_euclidean_budget_bound (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : 𝓢(ℂ, ℂ),
      derivativeBudget m (euclideanPullback h) ≤ C * planeDerivativeL2Budget (2 * m) h := by
  induction m with
  | zero =>
      refine ⟨1, zero_le_one, fun h => ?_⟩
      simp only [derivativeBudget, planeDerivativeL2Budget,
        norm_toLp_euclideanPullback, one_mul, le_refl]
  | succ m ih =>
      obtain ⟨C, hC, hbound⟩ := ih
      refine ⟨C * (1 + 2 * laplacianFactor), mul_nonneg hC
        (add_nonneg zero_le_one (mul_nonneg (by norm_num) laplacianFactor_nonneg)), fun h => ?_⟩
      have h0 := (hbound h).trans (mul_le_mul_of_nonneg_left
        (planeDerivativeL2Budget_mono (by omega : 2 * m ≤ 2 * (m + 1)) h) hC)
      have h2 (i : Fin 2) : derivativeBudget m (coordinateSecond i (euclideanPullback h)) ≤
          C * planeDerivativeL2Budget (2 * (m + 1)) h := by
        rw [coordinateSecond_euclideanPullback]
        exact (hbound _).trans (mul_le_mul_of_nonneg_left (budget_second_le m h i) hC)
      change derivativeBudget m (euclideanPullback h) +
          laplacianFactor *
            ∑ i : Fin 2, derivativeBudget m (coordinateSecond i (euclideanPullback h))
        ≤ _
      rw [Fin.sum_univ_two]
      calc
        _ ≤ C * planeDerivativeL2Budget (2 * (m + 1)) h + laplacianFactor *
            (C * planeDerivativeL2Budget (2 * (m + 1)) h +
              C * planeDerivativeL2Budget (2 * (m + 1)) h) :=
          _root_.add_le_add h0 (mul_le_mul_of_nonneg_left
            (_root_.add_le_add (h2 0) (h2 1)) laplacianFactor_nonneg)
        _ = _ := by ring

theorem exists_norm_iteratedFDeriv_le_planeDerivativeL2Budget (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : 𝓢(ℂ, ℂ)) (z : ℂ),
      ‖iteratedFDeriv ℝ j (h : ℂ → ℂ) z‖ ≤
        C * planeDerivativeL2Budget (2 * (j + 1)) h := by
  obtain ⟨C, hC, hbound⟩ := exists_euclidean_budget_bound (j + 1)
  have hdim : (2 : ℝ) < 2 * (2 * ((j + 1 : ℕ) : ℝ) - (j : ℝ)) := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) j]
  let K := (2 * Real.pi * ‖(-innerSL ℝ :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)‖) ^ j *
        ‖momentLp j hdim‖
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K * C, mul_nonneg hK hC, fun h z => ?_⟩
  have hSob := norm_iteratedFDeriv_schwartz_le_derivativeBudget (j + 1) j hdim
    (euclideanPullback h) (orthonormalBasisOneI.repr z)
  have heq : ‖iteratedFDeriv ℝ j (euclideanPullback h : EuclideanSpace ℝ (Fin 2) → ℂ)
      (orthonormalBasisOneI.repr z)‖ = ‖iteratedFDeriv ℝ j (h : ℂ → ℂ) z‖ := by
    change ‖iteratedFDeriv ℝ j ((h : ℂ → ℂ) ∘ orthonormalBasisOneI.repr.symm)
      (orthonormalBasisOneI.repr z)‖ = _
    rw [LinearIsometryEquiv.norm_iteratedFDeriv_comp_right]
    simp
  calc
    _ = _ := heq.symm
    _ ≤ K * derivativeBudget (j + 1) (euclideanPullback h) := hSob
    _ ≤ K * (C * planeDerivativeL2Budget (2 * (j + 1)) h) :=
      mul_le_mul_of_nonneg_left (hbound h) hK
    _ = _ := by ring

end Complex
