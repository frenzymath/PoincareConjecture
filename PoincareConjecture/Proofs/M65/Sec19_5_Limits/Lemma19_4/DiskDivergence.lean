import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.PolarDivergence
import PoincareConjecture.Proofs.M58.Cor18_28_PolarIntegration
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

set_option autoImplicit false

open Set MeasureTheory Real
open scoped Manifold ContDiff Topology intervalIntegral

namespace PoincareConjecture

theorem m65Integral_divergence_loopDisk
    (X : LoopPlane → LoopPlane)
    (hX : ∀ z ∈ loopDiskSet, ContDiffAt ℝ 1 X z) :
    (∫ z in loopDiskSet, ∑ i : Fin 2,
      inner ℝ ((fderiv ℝ X z) (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
      ∫ θ in (-π)..π, inner ℝ (X (Proofs.M58.angularPoint θ))
        (Proofs.M58.angularPoint θ) := by
  let v : Fin 2 → LoopPlane := EuclideanSpace.basisFun (Fin 2) ℝ
  let D : LoopPlane → ℝ := fun z => ∑ i : Fin 2, inner ℝ ((fderiv ℝ X z) (v i)) (v i)
  let polar : ℝ × ℝ → LoopPlane := fun p => p.1 • Proofs.M58.angularPoint p.2
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (-π) π
  let S : Set (ℝ × ℝ) := Ioc (0 : ℝ) 1 ×ˢ Ioo (-π) π
  let P : ℝ × ℝ → ℝ := Function.uncurry (m65PolarRadialFlux X)
  let Q : ℝ × ℝ → ℝ := Function.uncurry (m65PolarAngularFlux X)
  have hπ : -π ≤ π := by linarith [pi_pos]
  have hpolar : ContDiff ℝ 1 polar :=
    contDiff_fst.smul ((Proofs.M58.contDiff_angularPoint.of_le (by simp)).comp contDiff_snd)
  have hτ : ContDiff ℝ 1 Proofs.M58.angularVector := by
    apply contDiff_euclidean.mpr
    intro i
    fin_cases i
    · exact contDiff_sin.neg
    · exact contDiff_cos
  have hmem (p : ℝ × ℝ) (hp : p ∈ K) : polar p ∈ loopDiskSet := by
    rw [loopDiskSet, mem_closedBall_zero_iff]
    change ‖p.1 • Proofs.M58.angularPoint p.2‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hp.1.1,
      Proofs.M58.norm_angularPoint, mul_one]
    exact hp.1.2
  have hP (p : ℝ × ℝ) (hp : p ∈ K) : ContDiffAt ℝ 1 P p := by
    exact contDiffAt_fst.mul (((hX _ (hmem p hp)).comp p hpolar.contDiffAt).inner
      ℝ ((Proofs.M58.contDiff_angularPoint.of_le (by simp)).comp contDiff_snd).contDiffAt)
  have hQ (p : ℝ × ℝ) (hp : p ∈ K) : ContDiffAt ℝ 1 Q p := by
    exact ((hX _ (hmem p hp)).comp p hpolar.contDiffAt).inner ℝ
      (hτ.comp contDiff_snd).contDiffAt
  have hD (p : ℝ × ℝ) (hp : p ∈ K) :
      fderiv ℝ P p (1, 0) + fderiv ℝ Q p (0, 1) = p.1 * D (polar p) := by
    have hPr : fderiv ℝ P p (1, 0) =
        deriv (fun r : ℝ => m65PolarRadialFlux X r p.2) p.1 := by
      have h := ((hP p hp).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt p.1
        ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
      simpa +instances only [P, Function.comp_def, Function.uncurry_apply_pair, Prod.eta,
        id_eq] using! h.deriv.symm
    have hQr : fderiv ℝ Q p (0, 1) =
        deriv (fun t : ℝ => m65PolarAngularFlux X p.1 t) p.2 := by
      have h := ((hQ p hp).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt p.2
        ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
      simpa +instances only [Q, Function.comp_def, Function.uncurry_apply_pair, Prod.eta,
        id_eq] using! h.deriv.symm
    rw [hPr, hQr, m65PolarDivergencePointwise X (hX _ (hmem p hp)), m65PolarTrace_eq]
  have hweight : ContinuousOn (fun p : ℝ × ℝ => p.1 * D (polar p)) K := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    apply continuousAt_fst.mul
    have hDC : ContinuousAt D (polar p) := by
      have h (i : Fin 2) : ContinuousAt
          (fun z => inner ℝ ((fderiv ℝ X z) (v i)) (v i)) (polar p) :=
        (((hX _ (hmem p hp)).continuousAt_fderiv (by simp)).clm_apply
          continuousAt_const).inner continuousAt_const
      simpa +instances only [D, Fin.sum_univ_two, Pi.add_apply] using! (h 0).add (h 1)
    exact hDC.comp hpolar.continuous.continuousAt
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hweightInt : IntegrableOn (fun p : ℝ × ℝ => p.1 * D (polar p)) K :=
    hweight.integrableOn_compact hK
  have hdivInt : IntegrableOn
      (fun p : ℝ × ℝ => fderiv ℝ P p (1, 0) + fderiv ℝ Q p (0, 1)) K := by
    apply hweightInt.congr
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    exact (hD p hp).symm
  have hrect := integral2_divergence_prod_of_hasFDerivAt
    P Q (fderiv ℝ P) (fderiv ℝ Q) 0 (-π) 1 π
    (by
      rw [uIcc_of_le zero_le_one, uIcc_of_le hπ]
      exact fun p hp => (hP p hp).continuousAt.continuousWithinAt)
    (by
      rw [uIcc_of_le zero_le_one, uIcc_of_le hπ]
      exact fun p hp => (hQ p hp).continuousAt.continuousWithinAt)
    (by
      intro p hp
      simp only [min_eq_left zero_le_one, max_eq_right zero_le_one,
        min_eq_left hπ, max_eq_right hπ] at hp
      exact ((hP p (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self hp)).differentiableAt
        (by simp)).hasFDerivAt)
    (by
      intro p hp
      simp only [min_eq_left zero_le_one, max_eq_right zero_le_one,
        min_eq_left hπ, max_eq_right hπ] at hp
      exact ((hQ p (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self hp)).differentiableAt
        (by simp)).hasFDerivAt)
    (by simpa only [uIcc_of_le zero_le_one,
      uIcc_of_le hπ] using hdivInt)
  have hpolarInt : (∫ z in loopDiskSet, D z) =
      ∫ r in (0 : ℝ)..1, ∫ θ in (-π)..π, r * D (polar (r, θ)) := by
    rw [Proofs.M58.integral_loopDisk_polar]
    have hI : IntegrableOn (fun p : ℝ × ℝ => p.1 * D (polar p)) S :=
      hweightInt.mono_set (prod_mono Ioc_subset_Icc_self Ioo_subset_Icc_self)
    change (∫ p in Ioc (0 : ℝ) 1 ×ˢ Ioo (-π) π,
      p.1 * D (polar p) ∂volume.prod volume) = _
    rw [setIntegral_prod _ hI]
    rw [intervalIntegral.integral_of_le zero_le_one]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r _
    dsimp only
    rw [intervalIntegral.integral_of_le hπ,
      integral_Ioc_eq_integral_Ioo]
  change (∫ z in loopDiskSet, D z) = _
  rw [hpolarInt]
  have hid : (∫ r in (0 : ℝ)..1, ∫ θ in (-π)..π, r * D (polar (r, θ))) =
      ∫ r in (0 : ℝ)..1, ∫ θ in (-π)..π,
        fderiv ℝ P (r, θ) (1, 0) + fderiv ℝ Q (r, θ) (0, 1) := by
    apply intervalIntegral.integral_congr
    intro r hr
    apply intervalIntegral.integral_congr
    intro θ hθ
    apply (hD (r, θ) ?_).symm
    exact ⟨by simpa only [uIcc_of_le zero_le_one] using hr,
      by simpa only [uIcc_of_le hπ] using hθ⟩
  rw [hid, hrect]
  have hQedge : (fun r : ℝ => Q (r, π)) = fun r : ℝ => Q (r, -π) := by
    funext r
    simp [Q, m65PolarAngularFlux, Proofs.M58.angularPoint, Proofs.M58.angularVector]
  rw [hQedge, sub_self, zero_add]
  simp only [P, Function.uncurry_apply_pair, m65PolarRadialFlux,
    one_smul, one_mul, zero_mul, intervalIntegral.integral_zero, sub_zero]

end PoincareConjecture
