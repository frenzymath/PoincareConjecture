import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.RadialRectangle
import Mathlib.MeasureTheory.Integral.DivergenceTheorem






noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture.M64

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





theorem annulusRadialRectangle_integral_divergence
    {lo hi : ℝ} (hlh : lo ≤ hi) {O : Set LoopPlane} (hO : IsOpen O)
    (hdom : annulusRadialRectangle lo hi ⊆ O) {J0 J1 : LoopPlane → E}
    (hJ0 : ContDiffOn ℝ 1 J0 O) (hJ1 : ContDiffOn ℝ 1 J1 O) :
    (∫ p in annulusRadialRectangle lo hi,
      fderiv ℝ J0 p (EuclideanSpace.single (0 : Fin 2) 1) +
        fderiv ℝ J1 p (EuclideanSpace.single (1 : Fin 2) 1)) =
      ((∫ x in (0 : ℝ)..curvePeriod, J1 (annulusPoint x hi)) -
        ∫ x in (0 : ℝ)..curvePeriod, J1 (annulusPoint x lo)) +
      ((∫ y in lo..hi, J0 (annulusPoint curvePeriod y)) -
        ∫ y in lo..hi, J0 (annulusPoint 0 y)) := by
  let L : (ℝ × ℝ) →L[ℝ] LoopPlane :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (EuclideanSpace.single 0 1) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (EuclideanSpace.single 1 1)
  have hL (q : ℝ × ℝ) : L q = annulusPoint q.1 q.2 := by
    ext i
    fin_cases i <;> simp [L, annulusPoint]
  have hL0 : L (1, 0) = EuclideanSpace.single (0 : Fin 2) 1 := by simp [L]
  have hL1 : L (0, 1) = EuclideanSpace.single (1 : Fin 2) 1 := by simp [L]
  let D := fun p => fderiv ℝ J0 p (EuclideanSpace.single (0 : Fin 2) 1) +
    fderiv ℝ J1 p (EuclideanSpace.single (1 : Fin 2) 1)
  have hclosed (q : ℝ × ℝ) (hq : q ∈ Icc ((0 : ℝ), lo) (curvePeriod, hi)) :
      L q ∈ annulusRadialRectangle lo hi := by
    rw [hL]
    exact ⟨hq.1.1, hq.2.1, hq.1.2, hq.2.2⟩
  have hopen (q : ℝ × ℝ) (hq : q ∈ Ioo (0 : ℝ) curvePeriod ×ˢ Ioo lo hi) : L q ∈ O :=
    hdom (hclosed q ⟨⟨hq.1.1.le, hq.2.1.le⟩, hq.1.2.le, hq.2.2.le⟩)
  have hD0 := (hJ0.fderiv_of_isOpen hO (m := 0) (by norm_num)).continuousOn
  have hD1 := (hJ1.fderiv_of_isOpen hO (m := 0) (by norm_num)).continuousOn
  have hDc : ContinuousOn D O :=
    (hD0.clm_apply continuousOn_const).add (hD1.clm_apply continuousOn_const)
  have hDi : IntegrableOn D (annulusRadialRectangle lo hi) volume :=
    (hDc.mono hdom).integrableOn_compact (annulusRadialRectangle_isCompact lo hi)
  have hpi : IntegrableOn (fun q : ℝ × ℝ => D (L q))
      (Icc ((0 : ℝ), lo) (curvePeriod, hi)) volume := by
    change Integrable _ (volume.restrict _)
    simpa only [Function.comp_def, hL] using
      (annulusRadialRectangle_measurePreserving lo hi).integrable_comp_of_integrable hDi
  have hd0 (q : ℝ × ℝ) (hq : q ∈ Ioo (0 : ℝ) curvePeriod ×ˢ Ioo lo hi) :=
    (hJ0.contDiffAt (hO.mem_nhds (hopen q hq))).differentiableAt one_ne_zero
  have hd1 (q : ℝ × ℝ) (hq : q ∈ Ioo (0 : ℝ) curvePeriod ×ˢ Ioo lo hi) :=
    (hJ1.contDiffAt (hO.mem_nhds (hopen q hq))).differentiableAt one_ne_zero
  have hdiv := integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    (fun q => J0 (L q)) (fun q => J1 (L q))
    (fun q => (fderiv ℝ J0 (L q)).comp L) (fun q => (fderiv ℝ J1 (L q)).comp L)
    ((0 : ℝ), lo) (curvePeriod, hi)
    (show ((0 : ℝ), lo) ≤ (curvePeriod, hi) from
      ⟨by unfold curvePeriod; positivity, hlh⟩)
    (hJ0.continuousOn.comp L.continuous.continuousOn (fun q hq => hdom (hclosed q hq)))
    (hJ1.continuousOn.comp L.continuous.continuousOn (fun q hq => hdom (hclosed q hq)))
    (fun q hq => (hd0 q hq).hasFDerivAt.comp q L.hasFDerivAt)
    (fun q hq => (hd1 q hq).hasFDerivAt.comp q L.hasFDerivAt)
    (by simpa only [ContinuousLinearMap.comp_apply, hL0, hL1] using hpi)
  change (∫ p in annulusRadialRectangle lo hi, D p) = _
  rw [annulusRadialRectangle_integral]
  simpa only [D, ContinuousLinearMap.comp_apply, hL0, hL1, hL,
    sub_eq_add_neg, add_assoc] using hdiv




theorem annulusRadialRectangle_integral_divergence_periodic
    {lo hi : ℝ} (hlh : lo ≤ hi) {O : Set LoopPlane} (hO : IsOpen O)
    (hdom : annulusRadialRectangle lo hi ⊆ O) {J0 J1 : LoopPlane → E}
    (hJ0 : ContDiffOn ℝ 1 J0 O) (hJ1 : ContDiffOn ℝ 1 J1 O)
    (hseam : ∀ y ∈ Icc lo hi, J0 (annulusPoint curvePeriod y) = J0 (annulusPoint 0 y)) :
    (∫ p in annulusRadialRectangle lo hi,
      fderiv ℝ J0 p (EuclideanSpace.single (0 : Fin 2) 1) +
        fderiv ℝ J1 p (EuclideanSpace.single (1 : Fin 2) 1)) =
      (∫ x in (0 : ℝ)..curvePeriod, J1 (annulusPoint x hi)) -
        ∫ x in (0 : ℝ)..curvePeriod, J1 (annulusPoint x lo) := by
  rw [annulusRadialRectangle_integral_divergence hlh hO hdom hJ0 hJ1]
  have heq : (∫ y in lo..hi, J0 (annulusPoint curvePeriod y)) =
      ∫ y in lo..hi, J0 (annulusPoint 0 y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    exact hseam y (by simpa only [uIcc_of_le hlh] using hy)
  rw [heq, sub_self, add_zero]

end PoincareConjecture.M64
