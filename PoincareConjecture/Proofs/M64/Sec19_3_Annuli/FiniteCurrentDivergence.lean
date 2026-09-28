import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RectangleMeasurableIntegration
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.LipschitzAnnulusAdapter
import Mathlib.MeasureTheory.Integral.DivergenceTheorem





noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture

open Proofs.M58

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]






theorem m64Annulus_integral_divergence_of_continuous
    {J0 J1 : LoopPlane → E}
    (hc0 : ContinuousOn J0 m64AnnulusDomain)
    (hc1 : ContinuousOn J1 m64AnnulusDomain)
    (hd0 : ∀ p ∈ m64AnnulusInterior, DifferentiableAt ℝ J0 p)
    (hd1 : ∀ p ∈ m64AnnulusInterior, DifferentiableAt ℝ J1 p)
    (hi : IntegrableOn (fun p =>
      fderiv ℝ J0 p (EuclideanSpace.single (0 : Fin 2) 1) +
        fderiv ℝ J1 p (EuclideanSpace.single (1 : Fin 2) 1))
      m64AnnulusDomain volume) :
    (∫ p in m64AnnulusDomain,
      fderiv ℝ J0 p (EuclideanSpace.single (0 : Fin 2) 1) +
        fderiv ℝ J1 p (EuclideanSpace.single (1 : Fin 2) 1)) =
      ((∫ x in Icc (0 : ℝ) curvePeriod, J1 (annulusPoint x 1)) -
        ∫ x in Icc (0 : ℝ) curvePeriod, J1 (annulusPoint x 0)) +
      ((∫ y in Icc (0 : ℝ) 1, J0 (annulusPoint curvePeriod y)) -
        ∫ y in Icc (0 : ℝ) 1, J0 (annulusPoint 0 y)) := by
  let L : (ℝ × ℝ) →L[ℝ] LoopPlane :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (EuclideanSpace.single 0 1) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (EuclideanSpace.single 1 1)
  have hL (q : ℝ × ℝ) : L q = annulusPoint q.1 q.2 := by
    ext i
    fin_cases i <;> simp [L, annulusPoint]
  have hL0 : L (1, 0) = EuclideanSpace.single (0 : Fin 2) 1 := by simp [L]
  have hL1 : L (0, 1) = EuclideanSpace.single (1 : Fin 2) 1 := by simp [L]
  let D := fun p =>
    fderiv ℝ J0 p (EuclideanSpace.single (0 : Fin 2) 1) +
      fderiv ℝ J1 p (EuclideanSpace.single (1 : Fin 2) 1)
  have hclosed (q : ℝ × ℝ) (hq : q ∈ Icc ((0 : ℝ), (0 : ℝ)) (curvePeriod, 1)) :
      L q ∈ m64AnnulusDomain := by
    rw [hL]
    exact ⟨hq.1.1, hq.2.1, hq.1.2, hq.2.2⟩
  have hopen (q : ℝ × ℝ)
      (hq : q ∈ Ioo (0 : ℝ) curvePeriod ×ˢ Ioo (0 : ℝ) 1) :
      L q ∈ m64AnnulusInterior := by
    rw [hL]
    intro i _
    fin_cases i
    · exact hq.1
    · exact hq.2
  have hpi : IntegrableOn (fun q : ℝ × ℝ => D (L q))
      (Icc ((0 : ℝ), (0 : ℝ)) (curvePeriod, 1)) volume := by
    have h := m64AnnulusPoint_measurePreserving.integrable_comp_of_integrable
      (hi.mono_set interior_subset)
    simpa +instances only [IntegrableOn, Measure.prod_restrict, Icc_prod_eq, hL, D,
      Function.comp_def] using! h
  have hdiv := integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    (fun q => J0 (L q)) (fun q => J1 (L q))
    (fun q => (fderiv ℝ J0 (L q)).comp L) (fun q => (fderiv ℝ J1 (L q)).comp L)
    ((0 : ℝ), (0 : ℝ)) (curvePeriod, 1)
    (show ((0 : ℝ), (0 : ℝ)) ≤ (curvePeriod, 1) from
      ⟨by unfold curvePeriod; positivity, zero_le_one⟩)
    (hc0.comp L.continuous.continuousOn hclosed)
    (hc1.comp L.continuous.continuousOn hclosed)
    (fun q hq => (hd0 _ (hopen q hq)).hasFDerivAt.comp q L.hasFDerivAt)
    (fun q hq => (hd1 _ (hopen q hq)).hasFDerivAt.comp q L.hasFDerivAt)
    (by simpa only [ContinuousLinearMap.comp_apply, hL0, hL1] using hpi)
  have hpre : loopPlaneEquivProd.symm ⁻¹' m64AnnulusDomain =
      Icc ((0 : ℝ), (0 : ℝ)) (curvePeriod, 1) := by
    ext q
    change (0 ≤ q.1 ∧ q.1 ≤ curvePeriod ∧ 0 ≤ q.2 ∧ q.2 ≤ 1) ↔
      (0 ≤ q.1 ∧ 0 ≤ q.2) ∧ q.1 ≤ curvePeriod ∧ q.2 ≤ 1
    tauto
  have hint := measurePreserving_loopPlaneEquivProd.symm.setIntegral_preimage_emb
    loopPlaneEquivProd.symm.measurableEmbedding D m64AnnulusDomain
  rw [hpre] at hint
  have hmeasure : (∫ p in m64AnnulusDomain, D p) =
      ∫ q in Icc ((0 : ℝ), (0 : ℝ)) (curvePeriod, 1), D (L q) := by
    convert hint.symm using 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun q => congrArg D (hL q)
  rw [hmeasure]
  simp only [ContinuousLinearMap.comp_apply, hL0, hL1] at hdiv
  have hp : 0 ≤ curvePeriod := by unfold curvePeriod; positivity
  simp only [hL, intervalIntegral.integral_of_le hp,
    intervalIntegral.integral_of_le zero_le_one,
    setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))] at hdiv
  simpa only [D, hL, sub_eq_add_neg, add_assoc] using hdiv





theorem m64Annulus_integral_divergence_of_continuous_periodic
    {J0 J1 : LoopPlane → E}
    (hc0 : ContinuousOn J0 m64AnnulusDomain)
    (hc1 : ContinuousOn J1 m64AnnulusDomain)
    (hd0 : ∀ p ∈ m64AnnulusInterior, DifferentiableAt ℝ J0 p)
    (hd1 : ∀ p ∈ m64AnnulusInterior, DifferentiableAt ℝ J1 p)
    (hi : IntegrableOn (fun p =>
      fderiv ℝ J0 p (EuclideanSpace.single (0 : Fin 2) 1) +
        fderiv ℝ J1 p (EuclideanSpace.single (1 : Fin 2) 1))
      m64AnnulusDomain volume)
    (hseam : ∀ y ∈ Icc (0 : ℝ) 1,
      J0 (annulusPoint curvePeriod y) = J0 (annulusPoint 0 y)) :
    (∫ p in m64AnnulusDomain,
      fderiv ℝ J0 p (EuclideanSpace.single (0 : Fin 2) 1) +
        fderiv ℝ J1 p (EuclideanSpace.single (1 : Fin 2) 1)) =
      ∫ x in Icc (0 : ℝ) curvePeriod, J1 (annulusPoint x 1) - J1 (annulusPoint x 0) := by
  rw [m64Annulus_integral_divergence_of_continuous hc0 hc1 hd0 hd1 hi]
  have heq : (∫ y in Icc (0 : ℝ) 1, J0 (annulusPoint curvePeriod y)) =
      ∫ y in Icc (0 : ℝ) 1, J0 (annulusPoint 0 y) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact hseam y hy
  have htrace (y : ℝ) (hy : y ∈ Icc (0 : ℝ) 1) :
      IntegrableOn (fun x => J1 (annulusPoint x y)) (Icc (0 : ℝ) curvePeriod) volume := by
    have hline : Continuous (fun x : ℝ => annulusPoint x y) := by
      unfold annulusPoint
      fun_prop
    exact (hc1.comp hline.continuousOn
      (fun _ hx => ⟨hx.1, hx.2, hy.1, hy.2⟩)).integrableOn_compact isCompact_Icc
  rw [heq, sub_self, add_zero, integral_sub (htrace 1 (by simp)) (htrace 0 (by simp))]

end PoincareConjecture
