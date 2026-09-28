import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.DiskDivergence

set_option autoImplicit false

open Set MeasureTheory Real
open scoped ContDiff Topology intervalIntegral

namespace PoincareConjecture

theorem m65Integral_divergence_loopDisk_of_trace
    (X : LoopPlane → LoopPlane) (d : LoopPlane → ℝ)
    (hX : ContinuousOn X loopDiskSet)
    (hXi : ∀ z ∈ Metric.ball (0 : LoopPlane) 1, ContDiffAt ℝ 1 X z)
    (hd : ContinuousOn d loopDiskSet)
    (hdiv : ∀ z ∈ Metric.ball (0 : LoopPlane) 1,
      (∑ i : Fin 2, inner ℝ ((fderiv ℝ X z) (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) = d z) :
    (∫ z in loopDiskSet, d z) =
      ∫ θ in (-π)..π, inner ℝ (X (Proofs.M58.angularPoint θ))
        (Proofs.M58.angularPoint θ) := by
  let polar : ℝ × ℝ → LoopPlane := fun p => p.1 • Proofs.M58.angularPoint p.2
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (-π) π
  let O : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π
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
  have hmemi (p : ℝ × ℝ) (hp : p ∈ O) : polar p ∈ Metric.ball (0 : LoopPlane) 1 := by
    rw [mem_ball_zero_iff]
    change ‖p.1 • Proofs.M58.angularPoint p.2‖ < 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp.1.1,
      Proofs.M58.norm_angularPoint, mul_one]
    exact hp.1.2
  have hPC : ContinuousOn P K :=
    continuousOn_fst.mul ((hX.comp hpolar.continuous.continuousOn hmem).inner
      (Proofs.M58.contDiff_angularPoint.continuous.comp continuous_snd).continuousOn)
  have hQC : ContinuousOn Q K :=
    (hX.comp hpolar.continuous.continuousOn hmem).inner
      (hτ.continuous.comp continuous_snd).continuousOn
  have hP (p : ℝ × ℝ) (hp : p ∈ O) : ContDiffAt ℝ 1 P p :=
    contDiffAt_fst.mul (((hXi _ (hmemi p hp)).comp p hpolar.contDiffAt).inner
      ℝ ((Proofs.M58.contDiff_angularPoint.of_le (by simp)).comp contDiff_snd).contDiffAt)
  have hQ (p : ℝ × ℝ) (hp : p ∈ O) : ContDiffAt ℝ 1 Q p :=
    ((hXi _ (hmemi p hp)).comp p hpolar.contDiffAt).inner ℝ
      (hτ.comp contDiff_snd).contDiffAt
  have hD (p : ℝ × ℝ) (hp : p ∈ O) :
      fderiv ℝ P p (1, 0) + fderiv ℝ Q p (0, 1) = p.1 * d (polar p) := by
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
    rw [hPr, hQr, m65PolarDivergencePointwise X (hXi _ (hmemi p hp)), m65PolarTrace_eq,
      hdiv _ (hmemi p hp)]
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hWI : IntegrableOn (fun p : ℝ × ℝ => p.1 * d (polar p)) K :=
    (continuousOn_fst.mul (hd.comp hpolar.continuous.continuousOn hmem)).integrableOn_compact hK
  have hOK : O =ᵐ[volume] K :=
    Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc
  have hOae : ∀ᵐ p ∂volume.restrict K, p ∈ O := by
    rw [← Measure.restrict_congr_set hOK]
    exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
  have hDeq : (fun p : ℝ × ℝ => fderiv ℝ P p (1, 0) + fderiv ℝ Q p (0, 1))
      =ᵐ[volume.restrict K] fun p => p.1 * d (polar p) := by
    filter_upwards [hOae] with p hp
    exact hD p hp
  have hDI : IntegrableOn
      (fun p : ℝ × ℝ => fderiv ℝ P p (1, 0) + fderiv ℝ Q p (0, 1)) K :=
    hWI.congr hDeq.symm
  have hrect := integral2_divergence_prod_of_hasFDerivAt
    P Q (fderiv ℝ P) (fderiv ℝ Q) 0 (-π) 1 π
    (by simpa only [uIcc_of_le zero_le_one, uIcc_of_le hπ] using hPC)
    (by simpa only [uIcc_of_le zero_le_one, uIcc_of_le hπ] using hQC)
    (by
      intro p hp
      simp only [min_eq_left zero_le_one, max_eq_right zero_le_one,
        min_eq_left hπ, max_eq_right hπ] at hp
      exact ((hP p hp).differentiableAt (by simp)).hasFDerivAt)
    (by
      intro p hp
      simp only [min_eq_left zero_le_one, max_eq_right zero_le_one,
        min_eq_left hπ, max_eq_right hπ] at hp
      exact ((hQ p hp).differentiableAt (by simp)).hasFDerivAt)
    (by simpa only [uIcc_of_le zero_le_one, uIcc_of_le hπ] using hDI)
  have hprod : (∫ r in (0 : ℝ)..1, ∫ θ in (-π)..π,
      fderiv ℝ P (r, θ) (1, 0) + fderiv ℝ Q (r, θ) (0, 1)) =
      ∫ p in K, fderiv ℝ P p (1, 0) + fderiv ℝ Q p (0, 1) := by
    simp only [intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_of_le hπ,
      setIntegral_congr_set (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]
    exact (setIntegral_prod _ hDI).symm
  calc
    (∫ z in loopDiskSet, d z) = ∫ p in K, p.1 * d (polar p) := by
      rw [Proofs.M58.integral_loopDisk_polar]
      exact setIntegral_congr_set (Measure.set_prod_ae_eq Ioc_ae_eq_Icc Ioo_ae_eq_Icc)
    _ = ∫ p in K, fderiv ℝ P p (1, 0) + fderiv ℝ Q p (0, 1) :=
      integral_congr_ae hDeq.symm
    _ = _ := by
      rw [← hprod, hrect]
      have hQedge : (fun r : ℝ => Q (r, π)) = fun r : ℝ => Q (r, -π) := by
        funext r
        simp [Q, m65PolarAngularFlux, Proofs.M58.angularPoint, Proofs.M58.angularVector]
      rw [hQedge, sub_self, zero_add]
      simp only [P, Function.uncurry_apply_pair, m65PolarRadialFlux,
        one_smul, one_mul, zero_mul, intervalIntegral.integral_zero, sub_zero]

end PoincareConjecture
