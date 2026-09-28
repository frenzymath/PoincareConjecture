import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchGaugeWeakTransform
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchGaugeCutoff
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter MeasureTheory Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M65Branch




theorem dbar_eq_zero_of_differentiableAt_complex {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {F : ℂ → E} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) : dbar F z = 0 := by
  have hI := (differentiableAt_complex_iff_differentiableAt_real.mp hF).2
  change (2 : ℂ)⁻¹ • (fderiv ℝ F z 1 + I • fderiv ℝ F z I) = 0
  rw [hI, smul_smul, I_mul_I, neg_one_smul, add_neg_cancel, smul_zero]





theorem exists_C1_matrix_germ {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] [Nontrivial E]
    {A : ℂ → E →L[ℂ] E} {U : Set ℂ} {z0 : ℂ}
    (hU : IsOpen U) (hz0 : z0 ∈ U) (hA : ContDiffOn ℝ 1 A U) :
    ∃ (Q : ℂ → E →L[ℂ] E) (V : Set ℂ), IsOpen V ∧ z0 ∈ V ∧ V ⊆ U ∧
      ContDiff ℝ 1 Q ∧ (∀ z, IsUnit (Q z)) ∧
      ∀ z ∈ V, dbar Q z = A z * Q z := by
  let Ashift (z : ℂ) := A (z0 + z)
  let Ushift := (fun z : ℂ => z0 + z) ⁻¹' U
  have hshift : ContDiff ℝ 1 (fun z : ℂ => z0 + z) := contDiff_const.add contDiff_id
  have hUshift : IsOpen Ushift := hU.preimage hshift.continuous
  have h0 : (0 : ℂ) ∈ Ushift := by simpa only [Ushift, mem_preimage, add_zero] using hz0
  have hAshift : ContDiffOn ℝ 1 Ashift Ushift :=
    hA.comp hshift.contDiffOn (fun _ hz => hz)
  obtain ⟨A0, R, B0, B1, δ, hR, hB0, hB1, hδ, hA0, hs, hb, hd, hsmall, heq⟩ :=
    exists_small_compact_coefficient hUshift h0 hAshift
  have hQ0 := cauchyGauge_spec hR hB0 hB1 hδ hA0 hs hb hd hsmall
  let Q (z : ℂ) := cauchyGauge A0 (z - z0)
  have hback : ContDiff ℝ 1 (fun z : ℂ => z - z0) := contDiff_id.sub contDiff_const
  have hQ : ContDiff ℝ 1 Q := hQ0.1.comp hback
  obtain ⟨W, hW, hWopen, h0W⟩ := _root_.mem_nhds_iff.mp heq
  let V := U ∩ (fun z : ℂ => z - z0) ⁻¹' W
  have hzV : z0 ∈ V := ⟨hz0, by simpa only [mem_preimage, sub_self] using h0W⟩
  refine ⟨Q, V, hU.inter (hWopen.preimage hback.continuous), hzV,
    inter_subset_left, hQ, fun z => hQ0.2.2.2 (z - z0), ?_⟩
  intro z hz
  have hder := (hQ0.1.differentiable one_ne_zero (z - z0)).hasFDerivAt.comp z
    ((hasFDerivAt_id (𝕜 := ℝ) z).sub_const z0)
  change HasFDerivAt Q _ z at hder
  have hbar : dbar Q z = dbar (cauchyGauge A0) (z - z0) := by
    simp only [dbar, hder.fderiv, ContinuousLinearMap.comp_id]
  rw [hbar, hQ0.2.1, hW hz.2]
  have hcancel : z0 + (z - z0) = z := by abel
  simp only [Ashift, hcancel, Q]






theorem contDiffOn_of_weak_matrix_equation {n : ℕ} [Nonempty (Fin n)]
    {A : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)} {F : ℂ → Fin n → ℂ}
    {U : Set ℂ} (hU : IsOpen U) (hA : ContDiffOn ℝ 1 A U) (hF : Continuous F)
    (hG : ∀ i, LocallyIntegrable (fun z => A z (F z) i) volume)
    (hweak : ∀ i (φ : ℂ → ℂ), ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      (∫ z, dbar φ z * F z i) = -∫ z, φ z * A z (F z) i) :
    ContDiffOn ℝ 1 F U ∧ ∀ z ∈ U, dbar F z = A z (F z) := by
  have hlocal (z : ℂ) (hz : z ∈ U) :
      ContDiffAt ℝ 1 F z ∧ dbar F z = A z (F z) := by
    obtain ⟨Q, V, hV, hzV, hVU, hQ, hunit, heq⟩ := exists_C1_matrix_germ hU hz hA
    let H (w : ℂ) := Ring.inverse (Q w) (F w)
    have hH : DifferentiableOn ℂ H V := differentiableOn_inverse_weak_matrix_field
      hV hF hQ hunit heq hG (fun i φ hφ hs hφV => hweak i φ hφ hs (hφV.trans hVU))
    have hHz : ContDiffAt ℝ 1 H z :=
      ((hH.analyticAt (hV.mem_nhds hzV)).contDiffAt : ContDiffAt ℂ 1 H z).restrict_scalars ℝ
    have hidentity : (fun w => Q w (H w)) = F := by
      funext w
      change (Q w * Ring.inverse (Q w)) (F w) = F w
      rw [Ring.mul_inverse_cancel _ (hunit w)]
      rfl
    have hreal : ContDiffAt ℝ 1 F z := by
      rw [← hidentity]
      exact ((ContinuousLinearMap.restrictScalarsL ℂ
        (Fin n → ℂ) (Fin n → ℂ) ℝ ℝ).contDiff.contDiffAt.comp z hQ.contDiffAt).clm_apply hHz
    refine ⟨hreal, ?_⟩
    have hp := dbar_clm_apply (hQ.differentiable one_ne_zero z)
      (hHz.differentiableAt one_ne_zero)
    rw [hidentity, heq z hzV,
      dbar_eq_zero_of_differentiableAt_complex (hH.differentiableAt (hV.mem_nhds hzV)),
      map_zero, add_zero] at hp
    change dbar F z = A z (Q z (H z)) at hp
    simpa only [congrFun hidentity z] using hp
  exact ⟨fun z hz => (hlocal z hz).1.contDiffWithinAt, fun z hz => (hlocal z hz).2⟩





theorem cauchyGauge_contDiffOn_of_C1_coefficient {n : ℕ} [Nonempty (Fin n)]
    {A : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)} {R B0 : ℝ} {U : Set ℂ}
    (hR : 0 < R) (hB : 0 ≤ B0) (hA : AEStronglyMeasurable A volume)
    (hs : Function.support A ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ z, ‖A z‖ ≤ B0) (hsmall : 8 * R * B0 < 1 / 2)
    (hU : IsOpen U) (hAC1 : ContDiffOn ℝ 1 A U) :
    ContDiffOn ℝ 1 (cauchyGauge A) U ∧
      ∀ z ∈ U, dbar (cauchyGauge A) z = A z * cauchyGauge A z := by
  let E := Fin n → ℂ
  let P := cauchyGauge A
  have hP := cauchyGauge_measurable_spec hR hB hA hs hb hsmall
  have hPb (z : ℂ) : ‖P z‖ ≤ 2 := by
    have hh := norm_le_norm_sub_add (P z) (1 : E →L[ℂ] E)
    rw [norm_one] at hh
    linarith [hP.2.2.1 z]
  have hforce : AEStronglyMeasurable (fun z => A z * P z) volume :=
    hA.mul hP.1.aestronglyMeasurable
  have hforces : Function.support (fun z => A z * P z) ⊆ closedBall (0 : ℂ) R :=
    (Function.support_mul_subset_left _ _).trans hs
  have hforceb (z : ℂ) : ‖A z * P z‖ ≤ B0 * 2 :=
    (norm_mul_le _ _).trans (mul_le_mul (hb z) (hPb z) (norm_nonneg _) hB)
  have hcolumn (v : E) : ContDiffOn ℝ 1 (fun z => P z v) U ∧
      ∀ z ∈ U, dbar (fun w => P w v) z = A z (P z v) := by
    let L (i : Fin n) : (E →L[ℂ] E) →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.apply ℂ E v)
    have hF : Continuous (fun z => P z v) :=
      (ContinuousLinearMap.apply ℂ E v).continuous.comp hP.1
    apply contDiffOn_of_weak_matrix_equation hU hAC1 hF
    · intro i
      have hm := (L i).continuous.comp_aestronglyMeasurable hforce
      have hsup := (Function.support_comp_subset (map_zero (L i))
        (fun z => A z * P z)).trans hforces
      have hbound (z : ℂ) : ‖L i (A z * P z)‖ ≤ ‖L i‖ * (B0 * 2) :=
        ((L i).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (hforceb z) (norm_nonneg _))
      exact (memLp_one_iff_integrable.mp
        (memLp_of_bound_support hm hsup hbound 1)).locallyIntegrable
    · intro i φ hφ hφs _hφU
      exact cauchyGauge_weak_dbar_projection hR hB hA hs hb hsmall (L i) φ hφ hφs
  let T : (E →L[ℂ] E) ≃L[ℂ] (Fin n → E) := ContinuousLinearEquiv.piRing (Fin n)
  have hPc : ContDiffOn ℝ 1 P U := by
    have ht : ContDiffOn ℝ 1 (fun z => T (P z)) U :=
      contDiffOn_pi.mpr (fun j => (hcolumn (Pi.single j 1)).1)
    have hh := (T.symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp_contDiffOn ht
    change ContDiffOn ℝ 1 (fun z => T.symm (T (P z))) U at hh
    simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using hh
  refine ⟨hPc, ?_⟩
  intro z hz
  apply ContinuousLinearMap.ext
  intro v
  have hd := dbar_clm_comp (ContinuousLinearMap.apply ℂ E v)
    ((hPc.contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero)
  exact hd.symm.trans ((hcolumn v).2 z hz)

end PoincareConjecture.M65Branch
