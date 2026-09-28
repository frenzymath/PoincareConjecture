import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.DiskTraceDivergence
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityPolarMeasure

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Real
open scoped ContDiff Topology intervalIntegral

namespace PoincareConjecture.M65Gauss

theorem integral_divergence_loopDisk_off_countable
    (X : LoopPlane → LoopPlane) (d : LoopPlane → ℝ) (S : Set LoopPlane)
    (hS : S.Countable) (hX : ContinuousOn X loopDiskSet)
    (hXi : ∀ z ∈ Metric.ball (0 : LoopPlane) 1 \ S, ContDiffAt ℝ 1 X z)
    (hd : IntegrableOn d loopDiskSet)
    (hdiv : ∀ z ∈ Metric.ball (0 : LoopPlane) 1 \ S,
      (∑ i : Fin 2, inner ℝ ((fderiv ℝ X z) (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) = d z) :
    (∫ z in loopDiskSet, d z) =
      ∫ θ in (-π)..π, inner ℝ (X (Proofs.M58.angularPoint θ))
        (Proofs.M58.angularPoint θ) := by
  let polar : ℝ × ℝ → LoopPlane := fun p => p.1 • Proofs.M58.angularPoint p.2
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (-π) π
  let O : Set (ℝ × ℝ) := Ioo (0 : ℝ) 1 ×ˢ Ioo (-π) π
  let N := O ∩ polar ⁻¹' S
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
  have htarget (p : ℝ × ℝ) (hp : p ∈ O) : p ∈ polarCoord.target := ⟨hp.1.1, hp.2⟩
  have hpolar_inj : InjOn polar O := by
    intro p hp q hq heq
    apply polarCoord.symm.injOn (htarget p hp) (htarget q hq)
    apply Proofs.M58.loopPlaneEquivProd.symm.injective
    simpa only [Proofs.M58.loopPlaneEquivProd_symm_polar, polar] using heq
  have hN : N.Countable :=
    (show MapsTo polar N S from fun _ hp => hp.2).countable_of_injOn
      (hpolar_inj.mono inter_subset_left) hS
  have hbranch (p : ℝ × ℝ) (hp : p ∈ O \ N) :
      polar p ∈ Metric.ball (0 : LoopPlane) 1 \ S :=
    ⟨hmemi p hp.1, fun hs => hp.2 ⟨hp.1, hs⟩⟩
  have hPC : ContinuousOn P K :=
    continuousOn_fst.mul ((hX.comp hpolar.continuous.continuousOn hmem).inner (𝕜 := ℝ)
      (Proofs.M58.contDiff_angularPoint.continuous.comp continuous_snd).continuousOn)
  have hQC : ContinuousOn Q K :=
    (hX.comp hpolar.continuous.continuousOn hmem).inner (𝕜 := ℝ)
      (hτ.continuous.comp continuous_snd).continuousOn
  have hP (p : ℝ × ℝ) (hp : p ∈ O \ N) : ContDiffAt ℝ 1 P p :=
    contDiffAt_fst.mul (((hXi _ (hbranch p hp)).comp p hpolar.contDiffAt).inner
      ℝ ((Proofs.M58.contDiff_angularPoint.of_le (by simp)).comp contDiff_snd).contDiffAt)
  have hQ (p : ℝ × ℝ) (hp : p ∈ O \ N) : ContDiffAt ℝ 1 Q p :=
    ((hXi _ (hbranch p hp)).comp p hpolar.contDiffAt).inner ℝ
      (hτ.comp contDiff_snd).contDiffAt
  have hD (p : ℝ × ℝ) (hp : p ∈ O \ N) :
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
    rw [hPr, hQr, m65PolarDivergencePointwise X (hXi _ (hbranch p hp)),
      m65PolarTrace_eq, hdiv _ (hbranch p hp)]
  have hOK : O =ᵐ[volume] K :=
    Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc
  have hOae : ∀ᵐ p ∂volume.restrict K, p ∈ O := by
    rw [← Measure.restrict_congr_set hOK]
    exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
  let d0 := loopDiskSet.indicator d
  have hd0 : Integrable d0 := hd.integrable_indicator measurableSet_closedBall
  have hp0 : Integrable (fun p => d0 (M65Interior.polarPlane 0 p))
      M65Interior.polarMeasure :=
    (M65Interior.polarPlane_measurePreserving 0).integrable_comp_of_integrable (g := d0) hd0
  have hw0 : IntegrableOn (fun p : ℝ × ℝ => p.1 * d0 (polar p)) polarCoord.target := by
    have hh := (integrable_withDensity_iff_integrable_smul'
      (μ := volume.restrict polarCoord.target)
      (g := fun p => d0 (M65Interior.polarPlane 0 p))
      (measurable_fst.ennreal_ofReal) (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))).mp hp0
    apply hh.congr
    filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
    simp only [ENNReal.toReal_ofReal hp.1.le, smul_eq_mul, M65Interior.polarPlane,
      zero_add, polar]
  have hWO : IntegrableOn (fun p : ℝ × ℝ => p.1 * d (polar p)) O := by
    apply (hw0.mono_set htarget).congr_fun _ (measurableSet_Ioo.prod measurableSet_Ioo)
    intro p hp
    change p.1 * d0 (polar p) = p.1 * d (polar p)
    rw [show d0 (polar p) = d (polar p) from
      indicator_of_mem (Metric.ball_subset_closedBall (hmemi p hp)) d]
  have hWI : IntegrableOn (fun p : ℝ × ℝ => p.1 * d (polar p)) K :=
    (integrableOn_congr_set_ae hOK).mp hWO
  have hDeq : (fun p : ℝ × ℝ => fderiv ℝ P p (1, 0) + fderiv ℝ Q p (0, 1))
      =ᵐ[volume.restrict K] fun p => p.1 * d (polar p) := by
    filter_upwards [hOae, ae_restrict_of_ae (hN.ae_notMem volume)] with p hp hn
    exact hD p ⟨hp, hn⟩
  have hDI : IntegrableOn
      (fun p : ℝ × ℝ => fderiv ℝ P p (1, 0) + fderiv ℝ Q p (0, 1)) K :=
    hWI.congr hDeq.symm
  have hrect := integral2_divergence_prod_of_hasFDerivAt_off_countable
    P Q (fderiv ℝ P) (fderiv ℝ Q) 0 (-π) 1 π N hN
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

end PoincareConjecture.M65Gauss
