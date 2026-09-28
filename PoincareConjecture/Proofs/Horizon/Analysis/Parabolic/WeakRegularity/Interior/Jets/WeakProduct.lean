




import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.ConstantEnergy










open Set MeasureTheory
open scoped ContDiff

namespace Poincare.Analysis.Parabolic.WeakRegularity.Canonical


theorem weak_directional_derivative_mul_smooth
    {n : ℕ} {U : Set (Spacetime n)} (hU : IsOpen U)
    {q u w : Spacetime n → ℝ} (hq : ContDiff ℝ ∞ q) (v : Spacetime n)
    (hu : LocallyIntegrableOn u U volume)
    (hw : LocallyIntegrableOn w U volume)
    (hweak : ∀ ψ : Spacetime n → ℝ, ContDiff ℝ ∞ ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ U →
      (∫ y in U, ψ y * w y) = -(∫ y in U, fderiv ℝ ψ y v * u y)) :
    LocallyIntegrableOn (fun y => q y * u y) U volume ∧
    LocallyIntegrableOn (fun y => fderiv ℝ q y v * u y + q y * w y) U volume ∧
    ∀ φ : Spacetime n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ y in U, φ y * (fderiv ℝ q y v * u y + q y * w y)) =
        -(∫ y in U, fderiv ℝ φ y v * (q y * u y)) := by
  have hDq : ContDiff ℝ ∞ (fun y => fderiv ℝ q y v) :=
    (hq.fderiv_right (by simp)).clm_apply contDiff_const
  have hqu : LocallyIntegrableOn (fun y => q y * u y) U volume :=
    hu.continuousOn_mul hq.continuous.continuousOn hU.isLocallyClosed
  have hqw : LocallyIntegrableOn (fun y => q y * w y) U volume :=
    hw.continuousOn_mul hq.continuous.continuousOn hU.isLocallyClosed
  have hDqu : LocallyIntegrableOn (fun y => fderiv ℝ q y v * u y) U volume :=
    hu.continuousOn_mul hDq.continuous.continuousOn hU.isLocallyClosed
  refine ⟨hqu, hDqu.add hqw, ?_⟩
  intro φ hφ hφc hφU
  have integ {a ψ : Spacetime n → ℝ} (ha : LocallyIntegrableOn a U volume)
      (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U) :
      Integrable (fun y => ψ y * a y) (volume.restrict U) := by
    have hi : Integrable (fun y => ψ y * a y) := by
      apply (integrableOn_iff_integrable_of_support_subset
        ((Function.support_mul_subset_left ψ a).trans (subset_tsupport ψ))).mp
      exact (ha.integrableOn_compact_subset hψU hψc).continuousOn_mul
        hψ.continuous.continuousOn hψc
    exact hi.integrableOn
  have hDφ : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y v) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have htest := hweak (fun y => q y * φ y) (hq.mul hφ) hφc.mul_left
    (tsupport_mul_subset_right.trans hφU)
  have hder (y : Spacetime n) :
      fderiv ℝ (fun z => q z * φ z) y v = fderiv ℝ q y v * φ y + q y * fderiv ℝ φ y v := by
    rw [fderiv_fun_mul (hq.differentiable (by simp) y) (hφ.differentiable (by simp) y)]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
    ring
  have hsplit : (∫ y in U, fderiv ℝ (fun z => q z * φ z) y v * u y) =
      (∫ y in U, φ y * (fderiv ℝ q y v * u y)) +
        ∫ y in U, fderiv ℝ φ y v * (q y * u y) := by
    calc
      _ = ∫ y in U, φ y * (fderiv ℝ q y v * u y) +
          fderiv ℝ φ y v * (q y * u y) := by
        apply integral_congr_ae
        filter_upwards [] with y
        rw [hder]
        ring
      _ = _ := integral_add (integ hDqu hφ hφc hφU)
        (integ hqu hDφ (hφc.fderiv_apply ℝ v)
          ((tsupport_fderiv_apply_subset ℝ v).trans hφU))
  have hleft : (∫ y in U, (q y * φ y) * w y) = ∫ y in U, φ y * (q y * w y) := by
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  rw [hleft, hsplit] at htest
  simp only [mul_add]
  rw [integral_add (integ hDqu hφ hφc hφU) (integ hqw hφ hφc hφU)]
  linarith only [htest]

end Poincare.Analysis.Parabolic.WeakRegularity.Canonical
