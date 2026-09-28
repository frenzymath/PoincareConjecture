import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundTransfer










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace PoincareConjecture.M28.tube

open PoincareConjecture.SpacetimeBounds

private abbrev JE := EuclideanSpace ℝ (Fin 3)
private abbrev jb := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

private abbrev JMetric := MetricCoefficient 3
local instance : NormedAddCommGroup JMetric := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ JMetric := ContinuousLinearMap.toNormedSpace
private abbrev JFirst := JE →L[ℝ] JMetric
local instance : NormedAddCommGroup JFirst := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ JFirst := ContinuousLinearMap.toNormedSpace
private abbrev JSecond := JE →L[ℝ] JFirst
local instance : NormedAddCommGroup JSecond := ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ JSecond := ContinuousLinearMap.toNormedSpace

private def basisJetBound : ℝ :=
  1 + 3 * ‖jb.equivFunL.toContinuousLinearMap‖

private theorem one_le_basisJetBound : 1 ≤ basisJetBound := by
  dsimp [basisJetBound]
  linarith [norm_nonneg jb.equivFunL.toContinuousLinearMap]

private theorem norm_le_basisJetBound {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : JE →L[ℝ] F) {A : ℝ} (hA : 0 ≤ A)
    (hL : ∀ i : Fin 3, ‖L (EuclideanSpace.basisFun (Fin 3) ℝ i)‖ ≤ A) :
    ‖L‖ ≤ basisJetBound * A := by
  have h := jb.opNorm_le hA hL
  have h' : ‖L‖ ≤ (3 * ‖jb.equivFunL.toContinuousLinearMap‖) * A := by
    simpa [nsmul_eq_mul] using h
  apply h'.trans
  exact mul_le_mul_of_nonneg_right (by dsimp [basisJetBound]; linarith) hA




theorem exists_metricTwoJet_coefficient_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ (J : MetricTwoJet 3) (A : ℝ), 0 ≤ A →
      (∀ a b : Fin 3,
        |J.1 (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)| ≤ A) →
      (∀ i a b : Fin 3,
        |J.2.1 (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)| ≤ A) →
      (∀ j i a b : Fin 3,
        |J.2.2 (EuclideanSpace.basisFun (Fin 3) ℝ j)
          (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)| ≤ A) →
      ‖J‖ ≤ K * A := by
  have hC : 0 < basisJetBound := lt_of_lt_of_le (by norm_num) one_le_basisJetBound
  refine ⟨basisJetBound ^ 4, pow_pos hC _, ?_⟩
  intro J A hA hzero hfirst hsecond
  have h0 : ‖J.1‖ ≤ basisJetBound ^ 2 * A := by
    have h := norm_le_basisJetBound J.1 (by positivity : 0 ≤ basisJetBound * A)
      (fun a => norm_le_basisJetBound _ hA (fun b =>
        by simpa only [Real.norm_eq_abs] using hzero a b))
    simpa only [pow_two, mul_assoc] using h
  have h1 : ‖J.2.1‖ ≤ basisJetBound ^ 3 * A := by
    have h := norm_le_basisJetBound J.2.1
      (by positivity : 0 ≤ basisJetBound * (basisJetBound * A)) (fun i =>
        norm_le_basisJetBound _ (by positivity : 0 ≤ basisJetBound * A) (fun a =>
          norm_le_basisJetBound _ hA (fun b =>
            by simpa only [Real.norm_eq_abs] using hfirst i a b)))
    convert h using 1
    ring
  have h2 : ‖J.2.2‖ ≤ basisJetBound ^ 4 * A := by
    have h := norm_le_basisJetBound J.2.2
      (by positivity : 0 ≤ basisJetBound * (basisJetBound * (basisJetBound * A))) (fun j =>
        norm_le_basisJetBound _
          (by positivity : 0 ≤ basisJetBound * (basisJetBound * A)) (fun i =>
            norm_le_basisJetBound _ (by positivity : 0 ≤ basisJetBound * A) (fun a =>
              norm_le_basisJetBound _ hA (fun b =>
                by simpa only [Real.norm_eq_abs] using hsecond j i a b))))
    convert h using 1
    ring
  have h24 : basisJetBound ^ 2 ≤ basisJetBound ^ 4 :=
    pow_le_pow_right₀ one_le_basisJetBound (by omega)
  have h34 : basisJetBound ^ 3 ≤ basisJetBound ^ 4 :=
    pow_le_pow_right₀ one_le_basisJetBound (by omega)
  change max ‖J.1‖ (max ‖J.2.1‖ ‖J.2.2‖) ≤ _
  exact max_le (h0.trans (mul_le_mul_of_nonneg_right h24 hA))
    (max_le (h1.trans (mul_le_mul_of_nonneg_right h34 hA)) h2)

end PoincareConjecture.M28.tube
