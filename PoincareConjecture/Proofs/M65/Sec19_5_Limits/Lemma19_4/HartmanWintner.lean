import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchGaugeRegularity
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchLocalFactor
import Mathlib.Analysis.Complex.HasPrimitives

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter MeasureTheory Complex
open scoped Topology ContDiff Interval

namespace PoincareConjecture.M65Branch

private theorem rectangle_same_side {F : ℂ → ℂ} {U : Set ℂ}
    (hc : ContinuousOn F U)
    (hd : ∀ z ∈ U, z.im ≠ 0 → DifferentiableAt ℂ F z)
    {z w : ℂ} (hrect : Rectangle z w ⊆ U)
    (hside : (0 ≤ z.im ∧ 0 ≤ w.im) ∨ (z.im ≤ 0 ∧ w.im ≤ 0)) :
    wedgeIntegral z w F = -wedgeIntegral w z F := by
  rw [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq]
  apply integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
    F z w (hc.mono hrect)
  intro x hx
  have hxu : x ∈ U := hrect ⟨Ioo_subset_Icc_self hx.1, Ioo_subset_Icc_self hx.2⟩
  have hxi : x.im ≠ 0 := by
    rcases hside with hpos | hneg
    · have hmin : 0 ≤ min z.im w.im := le_min hpos.1 hpos.2
      exact ne_of_gt (hmin.trans_lt hx.2.1)
    · have hmax : max z.im w.im ≤ 0 := max_le hneg.1 hneg.2
      exact ne_of_lt (hx.2.2.trans_le hmax)
  exact (hd x hxu hxi).differentiableWithinAt

private theorem rectangle_crossing_real {F : ℂ → ℂ} {U : Set ℂ}
    (hc : ContinuousOn F U)
    (hd : ∀ z ∈ U, z.im ≠ 0 → DifferentiableAt ℂ F z)
    {z w : ℂ} (hrect : Rectangle z w ⊆ U) (hz : z.im ≤ 0) (hw : 0 ≤ w.im) :
    wedgeIntegral z w F = -wedgeIntegral w z F := by
  have hzw : z.im ≤ w.im := hz.trans hw
  have hlow : Rectangle z (w.re : ℂ) ⊆ Rectangle z w := by
    rintro x ⟨hx, hy⟩
    have hy' : z.im ≤ x.im ∧ x.im ≤ 0 := by
      simpa only [ofReal_im, uIcc_of_le hz, mem_preimage, mem_Icc] using hy
    exact ⟨by simpa only [ofReal_re] using hx,
      by simpa only [uIcc_of_le hzw, mem_preimage, mem_Icc] using
        And.intro hy'.1 (hy'.2.trans hw)⟩
  have hupp : Rectangle (z.re : ℂ) w ⊆ Rectangle z w := by
    rintro x ⟨hx, hy⟩
    have hy' : 0 ≤ x.im ∧ x.im ≤ w.im := by
      simpa only [ofReal_im, uIcc_of_le hw, mem_preimage, mem_Icc] using hy
    exact ⟨by simpa only [ofReal_re] using hx,
      by simpa only [uIcc_of_le hzw, mem_preimage, mem_Icc] using
        And.intro (hz.trans hy'.1) hy'.2⟩
  have hl := rectangle_same_side hc hd (hlow.trans hrect)
    (Or.inr ⟨hz, by simp⟩)
  have hu := rectangle_same_side hc hd (hupp.trans hrect)
    (Or.inl ⟨by simp, hw⟩)
  have hvertical (x : ℝ) (hx : x ∈ [[z.re, w.re]]) (a b : ℝ)
      (ha : a ∈ [[z.im, w.im]]) (hb : b ∈ [[z.im, w.im]]) :
      IntervalIntegrable (fun y : ℝ => F (x + y * I)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply hc.comp (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn
    intro y hy
    apply hrect
    have hy' := (uIcc_subset_uIcc ha hb) hy
    simpa [Rectangle, mem_reProdIm] using And.intro hx hy'
  have hzero : (0 : ℝ) ∈ [[z.im, w.im]] := by
    simpa only [uIcc_of_le hzw, mem_Icc] using And.intro hz hw
  have hleft := intervalIntegral.integral_add_adjacent_intervals
    (hvertical z.re left_mem_uIcc z.im 0 left_mem_uIcc hzero)
    (hvertical z.re left_mem_uIcc 0 w.im hzero right_mem_uIcc)
  have hright := intervalIntegral.integral_add_adjacent_intervals
    (hvertical w.re right_mem_uIcc z.im 0 left_mem_uIcc hzero)
    (hvertical w.re right_mem_uIcc 0 w.im hzero right_mem_uIcc)
  rw [← add_eq_zero_iff_eq_neg, wedgeIntegral_add_wedgeIntegral_eq] at hl hu ⊢
  simp only [ofReal_re, ofReal_im, ofReal_zero, zero_mul, add_zero] at hl hu
  rw [← hleft, ← hright]
  simp only [smul_eq_mul] at hl hu ⊢
  linear_combination hl + hu

theorem differentiableOn_of_continuousOn_off_real {F : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hc : ContinuousOn F U)
    (hd : ∀ z ∈ U, z.im ≠ 0 → DifferentiableAt ℂ F z) :
    DifferentiableOn ℂ F U := by
  apply (isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp
  refine ⟨?_, hc⟩
  have hordered (z w : ℂ) (hzw : z.im ≤ w.im) (hrect : Rectangle z w ⊆ U) :
      wedgeIntegral z w F = -wedgeIntegral w z F := by
    by_cases hz : 0 ≤ z.im
    · exact rectangle_same_side hc hd hrect (Or.inl ⟨hz, hz.trans hzw⟩)
    by_cases hw : w.im ≤ 0
    · exact rectangle_same_side hc hd hrect (Or.inr ⟨hzw.trans hw, hw⟩)
    exact rectangle_crossing_real hc hd hrect (le_of_not_ge hz) (le_of_not_ge hw)
  intro z w hrect
  by_cases hzw : z.im ≤ w.im
  · exact hordered z w hzw hrect
  · have hreverse : Rectangle w z ⊆ U := by
      simpa only [Rectangle, uIcc_comm] using hrect
    have hh := hordered w z (le_of_not_ge hzw) hreverse
    simpa only [neg_neg] using (congrArg Neg.neg hh).symm

private theorem inverse_matrix_differentiableAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {A Q : ℂ → E →L[ℂ] E} {F : ℂ → E} {z : ℂ}
    (hQ : ContDiffAt ℝ 1 Q z) (hunit : ∀ w, IsUnit (Q w))
    (hQeq : dbar Q z = A z * Q z) (hF : ContDiffAt ℝ 1 F z)
    (hFeq : dbar F z = A z (F z)) :
    DifferentiableAt ℂ (fun w => Ring.inverse (Q w) (F w)) z := by
  let H (w : ℂ) := Ring.inverse (Q w) (F w)
  have hidentity : (fun w => Q w (H w)) = F := by
    funext w
    change (Q w * Ring.inverse (Q w)) (F w) = F w
    rw [Ring.mul_inverse_cancel _ (hunit w)]
    rfl
  have hInv : ContDiffAt ℝ 1 (fun w => Ring.inverse (Q w)) z := by
    obtain ⟨u, hu⟩ := hunit z
    have hi : ContDiffAt ℝ 1 Ring.inverse (Q z) := by
      simpa only [hu] using contDiffAt_ringInverse ℝ (n := 1) u
    exact hi.comp z hQ
  let L := ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ
  have hRes := (L.contDiff (n := 1)).contDiffAt.comp z hInv
  have hH : DifferentiableAt ℝ H z :=
    (hRes.clm_apply hF).differentiableAt one_ne_zero
  have hp := dbar_clm_apply (hQ.differentiableAt one_ne_zero) hH
  rw [hidentity, hFeq, hQeq] at hp
  change A z (F z) = A z (Q z (H z)) + Q z (dbar H z) at hp
  rw [congrFun hidentity z] at hp
  have hzQ : Q z (dbar H z) = 0 := by
    apply add_left_cancel (a := A z (F z))
    simpa only [add_zero] using hp.symm
  have hzero := congrArg (fun v => (Ring.inverse (Q z) : E →L[ℂ] E) v) hzQ
  change (Ring.inverse (Q z) * Q z) (dbar H z) = Ring.inverse (Q z) 0 at hzero
  rw [Ring.inverse_mul_cancel _ (hunit z), map_zero] at hzero
  exact differentiableAt_complex_of_dbar_eq_zero hH hzero

theorem differentiableOn_inverse_cauchyGauge_off_real {n : ℕ} [Nonempty (Fin n)]
    {A : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)} {F : ℂ → Fin n → ℂ}
    {R B0 : ℝ} {U : Set ℂ}
    (hR : 0 < R) (hB : 0 ≤ B0) (hA : AEStronglyMeasurable A volume)
    (hs : Function.support A ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ z, ‖A z‖ ≤ B0) (hsmall : 8 * R * B0 < 1 / 2)
    (hU : IsOpen U) (hAC1 : ContDiffOn ℝ 1 A (U ∩ {z | z.im ≠ 0}))
    (hF : ContinuousOn F U) (hFC1 : ContDiffOn ℝ 1 F (U ∩ {z | z.im ≠ 0}))
    (heq : ∀ z ∈ U, z.im ≠ 0 → dbar F z = A z (F z)) :
    DifferentiableOn ℂ (fun z => Ring.inverse (cauchyGauge A z) (F z)) U := by
  let E := Fin n → ℂ
  let P := cauchyGauge A
  let H (z : ℂ) := Ring.inverse (P z) (F z)
  have hP := cauchyGauge_measurable_spec hR hB hA hs hb hsmall
  have hV : IsOpen (U ∩ {z : ℂ | z.im ≠ 0}) :=
    hU.inter (isOpen_ne_fun continuous_im continuous_const)
  have hPC1 := cauchyGauge_contDiffOn_of_C1_coefficient
    hR hB hA hs hb hsmall hV hAC1
  have hInv : Continuous (fun z => Ring.inverse (P z)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    obtain ⟨u, hu⟩ := hP.2.2.2 z
    have hi : ContDiffAt ℝ 1 Ring.inverse (P z) := by
      simpa only [hu] using contDiffAt_ringInverse ℝ (n := 1) u
    exact hi.continuousAt.comp (hP.1.continuousAt)
  have hH : ContinuousOn H U := by
    have hres := (ContinuousLinearMap.restrictScalarsL ℂ E E ℝ ℝ).continuous.comp hInv
    exact hres.continuousOn.clm_apply hF
  have hhol (z : ℂ) (hz : z ∈ U) (hzi : z.im ≠ 0) : DifferentiableAt ℂ H z :=
    inverse_matrix_differentiableAt
      (hPC1.1.contDiffAt (hV.mem_nhds ⟨hz, hzi⟩)) hP.2.2.2
      (hPC1.2 z ⟨hz, hzi⟩) (hFC1.contDiffAt (hV.mem_nhds ⟨hz, hzi⟩)) (heq z hz hzi)
  have hcoord (i : Fin n) : DifferentiableOn ℂ (fun z => H z i) U := by
    apply differentiableOn_of_continuousOn_off_real hU
      ((continuous_apply i).continuousOn.comp hH (fun _ _ => mem_univ _))
    intro z hz hzi
    exact (ContinuousLinearMap.proj i : E →L[ℂ] ℂ).differentiableAt.comp z (hhol z hz hzi)
  intro z hz
  exact differentiableWithinAt_pi.mpr (fun i => hcoord i z hz)

theorem exists_gauged_power_factor_off_real {n : ℕ} [Nonempty (Fin n)]
    {A : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)} {F : ℂ → Fin n → ℂ}
    {R B0 : ℝ} {U : Set ℂ}
    (hR : 0 < R) (hB : 0 ≤ B0) (hA : AEStronglyMeasurable A volume)
    (hs : Function.support A ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ z, ‖A z‖ ≤ B0) (hsmall : 8 * R * B0 < 1 / 2)
    (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U)
    (hAC1 : ContDiffOn ℝ 1 A (U ∩ {z | z.im ≠ 0}))
    (hF : ContinuousOn F U) (hFC1 : ContDiffOn ℝ 1 F (U ∩ {z | z.im ≠ 0}))
    (heq : ∀ z ∈ U, z.im ≠ 0 → dbar F z = A z (F z))
    (hnot : ¬∀ᶠ z in 𝓝 (0 : ℂ), F z = 0) :
    ∃ (m : ℕ) (g : ℂ → Fin n → ℂ), AnalyticAt ℂ g 0 ∧ g 0 ≠ 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), F z = z ^ m • cauchyGauge A z (g z) := by
  let H (z : ℂ) := Ring.inverse (cauchyGauge A z) (F z)
  have hP := cauchyGauge_measurable_spec hR hB hA hs hb hsmall
  have hidentity (z : ℂ) : cauchyGauge A z (H z) = F z := by
    change (cauchyGauge A z * Ring.inverse (cauchyGauge A z)) (F z) = F z
    rw [Ring.mul_inverse_cancel _ (hP.2.2.2 z)]
    rfl
  have hH : AnalyticAt ℂ H 0 :=
    (differentiableOn_inverse_cauchyGauge_off_real hR hB hA hs hb hsmall
      hU hAC1 hF hFC1 heq).analyticAt (hU.mem_nhds h0)
  have hnotH : ¬∀ᶠ z in 𝓝 (0 : ℂ), H z = 0 := by
    intro hh
    apply hnot
    filter_upwards [hh] with z hz
    rw [← hidentity z, hz, map_zero]
  obtain ⟨m, g, hg, hg0, hfactor⟩ := hH.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnotH
  refine ⟨m, g, hg, hg0, ?_⟩
  filter_upwards [hfactor] with z hz
  rw [← hidentity z, hz, sub_zero, map_smul]

noncomputable def reflectionOperator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : E ≃ₗᵢ[ℝ] E) (hJ : ∀ (c : ℂ) v, J (c • v) = star c • J v)
    (A : E →L[ℂ] E) : E →L[ℂ] E where
  toFun v := J (A (J v))
  map_add' v w := by simp only [map_add]
  map_smul' c v := by simp only [hJ, map_smul, star_star, RingHom.id_apply]
  cont := J.continuous.comp (A.continuous.comp J.continuous)

noncomputable def reflectionOperatorL {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : E ≃ₗᵢ[ℝ] E) (hJ : ∀ (c : ℂ) v, J (c • v) = star c • J v) :
    (E →L[ℂ] E) →L[ℝ] (E →L[ℂ] E) :=
  LinearMap.mkContinuous
    { toFun := reflectionOperator J hJ
      map_add' := by
        intro A B
        ext v
        simp only [reflectionOperator, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
          AddHom.coe_mk, add_apply, map_add]
      map_smul' := by
        intro r A
        ext v
        simp only [reflectionOperator, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
          AddHom.coe_mk, smul_apply, map_smul, RingHom.id_apply] }
    1 (fun A => by
      rw [one_mul]
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
      intro v
      change ‖J (A (J v))‖ ≤ ‖A‖ * ‖v‖
      simpa only [J.norm_map] using A.le_opNorm (J v))

theorem dbar_reflected {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : E ≃ₗᵢ[ℝ] E) (hJ : ∀ (c : ℂ) v, J (c • v) = star c • J v)
    {F : ℂ → E} {z : ℂ} (hF : DifferentiableAt ℝ F (star z)) :
    dbar (fun w => J (F (star w))) z = J (dbar F (star z)) := by
  let L := J.toContinuousLinearEquiv.toContinuousLinearMap
  have hd0 := hF.hasFDerivAt.comp z conjCLE.hasFDerivAt
  have hd := L.hasFDerivAt.comp z hd0
  change HasFDerivAt (fun w => J (F (star w))) _ z at hd
  simp only [dbar, hd.fderiv, dbarLinear, smul_apply, add_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, conjCLE_apply, map_one, conj_I,
    map_neg, L, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    map_add, hJ]
  simp

noncomputable def reflectedField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : E ≃ₗᵢ[ℝ] E) (F : ℂ → E) (z : ℂ) : E :=
  if 0 ≤ z.im then F z else J (F (star z))

noncomputable def reflectedCoefficient {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : E ≃ₗᵢ[ℝ] E) (hJ : ∀ (c : ℂ) v, J (c • v) = star c • J v)
    (A : ℂ → E →L[ℂ] E) (z : ℂ) : E →L[ℂ] E :=
  if 0 ≤ z.im then A z else reflectionOperator J hJ (A (star z))

theorem reflectedField_continuousOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : E ≃ₗᵢ[ℝ] E) {F : ℂ → E} {r : ℝ}
    (hc : ContinuousOn F (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hreal : ∀ z ∈ closedBall (0 : ℂ) r, z.im = 0 → J (F z) = F z) :
    ContinuousOn (reflectedField J F) (closedBall (0 : ℂ) r) := by
  classical
  let S : Set ℂ := {z | 0 ≤ z.im}
  have hS : IsClosed S := isClosed_le continuous_const continuous_im
  have hlow : closure Sᶜ ⊆ {z : ℂ | z.im ≤ 0} := by
    apply closure_minimal _ (isClosed_le continuous_im continuous_const)
    intro z hz
    change ¬0 ≤ z.im at hz
    exact le_of_not_ge hz
  have hupper : ContinuousOn F (closedBall (0 : ℂ) r ∩ closure S) := by
    simpa only [hS.closure_eq] using hc
  have hbottom : ContinuousOn (fun z => J (F (star z)))
      (closedBall (0 : ℂ) r ∩ closure Sᶜ) := by
    apply J.continuous.comp_continuousOn
    apply hc.comp continuous_star.continuousOn
    intro z hz
    refine ⟨?_, ?_⟩
    · simpa only [mem_closedBall_zero_iff, norm_star] using hz.1
    · have hi : z.im ≤ 0 := hlow hz.2
      change 0 ≤ (star z).im
      simpa only [star_def, conj_im, neg_nonneg] using hi
  have hboundary (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) r ∩ frontier S) :
      F z = J (F (star z)) := by
    have hnonneg : 0 ≤ z.im := hS.frontier_subset hz.2
    have hnonpos : z.im ≤ 0 := hlow (by
      rw [frontier_eq_closure_inter_closure] at hz
      exact hz.2.2)
    have him : z.im = 0 := le_antisymm hnonpos hnonneg
    have hstar : star z = z := by
      apply Complex.ext
      · simp
      · simp [him]
    rw [hstar]
    exact (hreal z hz.1 him).symm
  exact hupper.piecewise hboundary hbottom

private theorem half_piecewise_contDiffOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : ℂ → E} {U : Set ℂ} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F (U ∩ {z | 0 < z.im}))
    (hG : ContDiffOn ℝ 1 G (U ∩ {z | z.im < 0})) :
    ContDiffOn ℝ 1 (fun z => if 0 ≤ z.im then F z else G z)
      (U ∩ {z | z.im ≠ 0}) := by
  intro z hz
  rcases lt_or_gt_of_ne hz.2 with hneg | hpos
  · have hlocal : (fun w => if 0 ≤ w.im then F w else G w) =ᶠ[𝓝 z] G := by
      filter_upwards [continuous_im.continuousAt.eventually (gt_mem_nhds hneg)] with w hw
      exact if_neg (not_le.mpr hw)
    exact ((hG.contDiffAt ((hU.inter (isOpen_lt continuous_im continuous_const)).mem_nhds
      ⟨hz.1, hneg⟩)).congr_of_eventuallyEq hlocal).contDiffWithinAt
  · have hlocal : (fun w => if 0 ≤ w.im then F w else G w) =ᶠ[𝓝 z] F := by
      filter_upwards [continuous_im.continuousAt.eventually (lt_mem_nhds hpos)] with w hw
      exact if_pos hw.le
    exact ((hF.contDiffAt ((hU.inter (isOpen_lt continuous_const continuous_im)).mem_nhds
      ⟨hz.1, hpos⟩)).congr_of_eventuallyEq hlocal).contDiffWithinAt

theorem reflectedField_contDiffOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : E ≃ₗᵢ[ℝ] E) {F : ℂ → E} {r : ℝ}
    (hF : ContDiffOn ℝ 1 F (ball (0 : ℂ) r ∩ {z | 0 < z.im})) :
    ContDiffOn ℝ 1 (reflectedField J F) (ball (0 : ℂ) r ∩ {z | z.im ≠ 0}) := by
  apply half_piecewise_contDiffOn isOpen_ball hF
  apply J.toContinuousLinearEquiv.contDiff.comp_contDiffOn
  apply hF.comp conjCLE.contDiff.contDiffOn
  intro z hz
  refine ⟨?_, ?_⟩
  · simpa only [mem_ball_zero_iff, conjCLE_apply, norm_conj] using hz.1
  · simpa only [mem_ofPred_eq, conjCLE_apply, conj_im, neg_pos] using hz.2

theorem reflectedCoefficient_contDiffOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : E ≃ₗᵢ[ℝ] E) (hJ : ∀ (c : ℂ) v, J (c • v) = star c • J v)
    {A : ℂ → E →L[ℂ] E} {r : ℝ}
    (hA : ContDiffOn ℝ 1 A (ball (0 : ℂ) r ∩ {z | 0 < z.im})) :
    ContDiffOn ℝ 1 (reflectedCoefficient J hJ A)
      (ball (0 : ℂ) r ∩ {z | z.im ≠ 0}) := by
  apply half_piecewise_contDiffOn isOpen_ball hA
  apply (reflectionOperatorL J hJ).contDiff.comp_contDiffOn
  apply hA.comp conjCLE.contDiff.contDiffOn
  intro z hz
  refine ⟨?_, ?_⟩
  · simpa only [mem_ball_zero_iff, conjCLE_apply, norm_conj] using hz.1
  · simpa only [mem_ofPred_eq, conjCLE_apply, conj_im, neg_pos] using hz.2

theorem reflectedField_equation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : E ≃ₗᵢ[ℝ] E) (hJ : ∀ (c : ℂ) v, J (c • v) = star c • J v)
    (hJJ : Function.Involutive J) {F : ℂ → E} {A : ℂ → E →L[ℂ] E} {r : ℝ}
    (hF : ContDiffOn ℝ 1 F (ball (0 : ℂ) r ∩ {z | 0 < z.im}))
    (heq : ∀ z ∈ ball (0 : ℂ) r, 0 < z.im → dbar F z = A z (F z))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) (hzi : z.im ≠ 0) :
    dbar (reflectedField J F) z =
      reflectedCoefficient J hJ A z (reflectedField J F z) := by
  rcases lt_or_gt_of_ne hzi with hneg | hpos
  · have hlocal : reflectedField J F =ᶠ[𝓝 z] fun w => J (F (star w)) := by
      filter_upwards [continuous_im.continuousAt.eventually (gt_mem_nhds hneg)] with w hw
      exact if_neg (not_le.mpr hw)
    have hconj : star z ∈ ball (0 : ℂ) r := by
      simpa only [mem_ball_zero_iff, norm_star] using hz
    have hposconj : 0 < (star z).im := by simpa only [star_def, conj_im, neg_pos] using hneg
    have hreg := hF.contDiffAt ((isOpen_ball.inter
      (isOpen_lt continuous_const continuous_im)).mem_nhds ⟨hconj, hposconj⟩)
    have hdiff := hreg.differentiableAt one_ne_zero
    have hbar : dbar (reflectedField J F) z = dbar (fun w => J (F (star w))) z :=
      congrArg dbarLinear hlocal.fderiv_eq
    rw [hbar, dbar_reflected J hJ hdiff, heq (star z) hconj hposconj]
    simp only [reflectedCoefficient, reflectedField, if_neg (not_le.mpr hneg),
      reflectionOperator, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
      AddHom.coe_mk]
    rw [hJJ (F (star z))]
  · have hlocal : reflectedField J F =ᶠ[𝓝 z] F := by
      filter_upwards [continuous_im.continuousAt.eventually (lt_mem_nhds hpos)] with w hw
      exact if_pos hw.le
    have hbar : dbar (reflectedField J F) z = dbar F z :=
      congrArg dbarLinear hlocal.fderiv_eq
    rw [hbar, heq z hz hpos]
    simp only [reflectedCoefficient, reflectedField, if_pos hpos.le]

theorem exists_small_reflected_coefficient {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (J : E ≃ₗᵢ[ℝ] E) (hJ : ∀ (c : ℂ) v, J (c • v) = star c • J v)
    {A : ℂ → E →L[ℂ] E} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn A (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hAC1 : ContDiffOn ℝ 1 A (ball (0 : ℂ) r ∩ {z | 0 < z.im})) :
    ∃ (A0 : ℂ → E →L[ℂ] E) (R B0 : ℝ),
      0 < R ∧ R < r ∧ 0 ≤ B0 ∧ AEStronglyMeasurable A0 volume ∧
      Function.support A0 ⊆ closedBall (0 : ℂ) R ∧
      (∀ z, ‖A0 z‖ ≤ B0) ∧ 8 * R * B0 < 1 / 2 ∧
      ContDiffOn ℝ 1 A0 (ball (0 : ℂ) R ∩ {z | z.im ≠ 0}) ∧
      ∀ z ∈ ball (0 : ℂ) R, A0 z = reflectedCoefficient J hJ A z := by
  classical
  have hupper : IsClosed {z : ℂ | 0 ≤ z.im} :=
    isClosed_le continuous_const continuous_im
  have hK := (isCompact_closedBall (0 : ℂ) r).inter_right hupper
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  let B0 := max C 0
  have hB : 0 ≤ B0 := le_max_right _ _
  have hbound (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}) :
      ‖A z‖ ≤ B0 := (hC z hz).trans (le_max_left _ _)
  obtain ⟨rho, hrho, hsmallrho⟩ := exists_pos_mul_lt
    (by norm_num : (0 : ℝ) < 1 / 2) (8 * B0)
  obtain ⟨R, hR, hRlt⟩ := exists_between (lt_min hr hrho)
  have hRr : R < r := hRlt.trans_le (min_le_left _ _)
  have hRrho : R < rho := hRlt.trans_le (min_le_right _ _)
  have hsmall : 8 * R * B0 < 1 / 2 := by
    calc
      _ = (8 * B0) * R := by ring
      _ ≤ (8 * B0) * rho := mul_le_mul_of_nonneg_left hRrho.le (by positivity)
      _ < _ := hsmallrho
  let K := closedBall (0 : ℂ) R ∩ {z | 0 ≤ z.im}
  have hKm : MeasurableSet K := isClosed_closedBall.measurableSet.inter hupper.measurableSet
  have hKsub : K ⊆ closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im} :=
    fun _ hz => ⟨closedBall_subset_closedBall hRr.le hz.1, hz.2⟩
  let D := K.indicator A
  have hDm : AEStronglyMeasurable D volume :=
    (aestronglyMeasurable_indicator_iff hKm).mpr ((hc.mono hKsub).aestronglyMeasurable hKm)
  have hDb (z : ℂ) : ‖D z‖ ≤ B0 := by
    by_cases hz : z ∈ K
    · simpa only [D, indicator_of_mem hz] using hbound z (hKsub hz)
    · simpa only [D, indicator_of_notMem hz, norm_zero] using hB
  have hDeq (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) R) (hi : 0 ≤ z.im) :
      D z = A z := indicator_of_mem (show z ∈ K from ⟨hz, hi⟩) A
  let A0 := reflectedCoefficient J hJ D
  have hA0m : AEStronglyMeasurable A0 volume := by
    have hDmstar := hDm.comp_quasiMeasurePreserving conjLIE.measurePreserving.quasiMeasurePreserving
    have hreflect := (reflectionOperatorL J hJ).continuous.comp_aestronglyMeasurable hDmstar
    exact AEStronglyMeasurable.piecewise hupper.measurableSet hDm.restrict hreflect.restrict
  have hnorm (T : E →L[ℂ] E) : ‖reflectionOperator J hJ T‖ ≤ ‖T‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T)
    intro v
    change ‖J (T (J v))‖ ≤ ‖T‖ * ‖v‖
    simpa only [J.norm_map] using T.le_opNorm (J v)
  have hA0b (z : ℂ) : ‖A0 z‖ ≤ B0 := by
    dsimp only [A0, reflectedCoefficient]
    split_ifs
    · exact hDb z
    · exact (hnorm _).trans (hDb (star z))
  have hA0s : Function.support A0 ⊆ closedBall (0 : ℂ) R := by
    intro z hz
    by_contra hnot
    have hDz : D z = 0 := indicator_of_notMem (fun h => hnot h.1) A
    have hDs : D (star z) = 0 := by
      apply indicator_of_notMem
      intro h
      apply hnot
      simpa only [mem_closedBall_zero_iff, norm_star] using h.1
    have hzero : A0 z = 0 := by
      dsimp only [A0, reflectedCoefficient]
      split_ifs
      · exact hDz
      · rw [hDs]
        apply ContinuousLinearMap.ext
        intro v
        change J ((0 : E →L[ℂ] E) (J v)) = 0
        simp
    exact hz hzero
  have heq (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) :
      A0 z = reflectedCoefficient J hJ A z := by
    by_cases hi : 0 ≤ z.im
    · dsimp only [A0, reflectedCoefficient]
      rw [if_pos hi, if_pos hi, hDeq z (ball_subset_closedBall hz) hi]
    · have hsball : star z ∈ closedBall (0 : ℂ) R := by
        simpa only [mem_closedBall_zero_iff, norm_star] using ball_subset_closedBall hz
      have hsi : 0 ≤ (star z).im := by
        simpa only [star_def, conj_im, neg_nonneg] using le_of_not_ge hi
      dsimp only [A0, reflectedCoefficient]
      rw [if_neg hi, if_neg hi, hDeq (star z) hsball hsi]
  have hA0C1 : ContDiffOn ℝ 1 A0 (ball (0 : ℂ) R ∩ {z | z.im ≠ 0}) := by
    have hAr : ContDiffOn ℝ 1 A (ball (0 : ℂ) R ∩ {z | 0 < z.im}) :=
      hAC1.mono (fun _ hz => ⟨ball_subset_ball hRr.le hz.1, hz.2⟩)
    exact (reflectedCoefficient_contDiffOn J hJ hAr).congr (fun z hz => heq z hz.1)
  exact ⟨A0, R, B0, hR, hRr, hB, hA0m, hA0s, hA0b, hsmall, hA0C1, heq⟩

theorem exists_half_disk_power_factor {n : ℕ} [Nonempty (Fin n)]
    (J : (Fin n → ℂ) ≃ₗᵢ[ℝ] (Fin n → ℂ))
    (hJ : ∀ (c : ℂ) v, J (c • v) = star c • J v)
    (hJJ : Function.Involutive J)
    {F : ℂ → Fin n → ℂ} {A : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)} {r : ℝ}
    (hr : 0 < r)
    (hF : ContinuousOn F (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hFC1 : ContDiffOn ℝ 1 F (ball (0 : ℂ) r ∩ {z | 0 < z.im}))
    (hA : ContinuousOn A (closedBall (0 : ℂ) r ∩ {z | 0 ≤ z.im}))
    (hAC1 : ContDiffOn ℝ 1 A (ball (0 : ℂ) r ∩ {z | 0 < z.im}))
    (heq : ∀ z ∈ ball (0 : ℂ) r, 0 < z.im → dbar F z = A z (F z))
    (hreal : ∀ z ∈ closedBall (0 : ℂ) r, z.im = 0 → J (F z) = F z) :
    ∃ (A0 : ℂ → (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) (R B0 : ℝ),
      0 < R ∧ R < r ∧ 0 ≤ B0 ∧ AEStronglyMeasurable A0 volume ∧
      Function.support A0 ⊆ closedBall (0 : ℂ) R ∧
      (∀ z, ‖A0 z‖ ≤ B0) ∧ 8 * R * B0 < 1 / 2 ∧
      ContDiffOn ℝ 1 A0 (ball (0 : ℂ) R ∩ {z | z.im ≠ 0}) ∧
      (∀ z ∈ ball (0 : ℂ) R, A0 z = reflectedCoefficient J hJ A z) ∧
      ((∀ᶠ z in 𝓝[{z : ℂ | 0 ≤ z.im}] 0, F z = 0) ∨
        ∃ (m : ℕ) (g : ℂ → Fin n → ℂ), AnalyticAt ℂ g 0 ∧ g 0 ≠ 0 ∧
          cauchyGauge A0 0 (g 0) ≠ 0 ∧
          ContinuousAt (fun z => cauchyGauge A0 z (g z)) 0 ∧
          ∀ᶠ z in 𝓝[{z : ℂ | 0 ≤ z.im}] 0,
            F z = z ^ m • cauchyGauge A0 z (g z)) := by
  classical
  obtain ⟨A0, R, B0, hR, hRr, hB, hA0m, hA0s, hA0b, hsmall, hA0C1, hA0eq⟩ :=
    exists_small_reflected_coefficient J hJ hr hA hAC1
  refine ⟨A0, R, B0, hR, hRr, hB, hA0m, hA0s, hA0b, hsmall, hA0C1, hA0eq, ?_⟩
  let F0 := reflectedField J F
  have hF0 : ContinuousOn F0 (ball (0 : ℂ) R) :=
    (reflectedField_continuousOn J hF hreal).mono
      (fun _ hz => closedBall_subset_closedBall hRr.le (ball_subset_closedBall hz))
  have hF0C1 : ContDiffOn ℝ 1 F0 (ball (0 : ℂ) R ∩ {z | z.im ≠ 0}) :=
    (reflectedField_contDiffOn J hFC1).mono
      (fun _ hz => ⟨ball_subset_ball hRr.le hz.1, hz.2⟩)
  have hF0eq (z : ℂ) (hz : z ∈ ball (0 : ℂ) R) (hi : z.im ≠ 0) :
      dbar F0 z = A0 z (F0 z) := by
    rw [hA0eq z hz]
    exact reflectedField_equation J hJ hJJ hFC1 heq (ball_subset_ball hRr.le hz) hi
  by_cases hzero : ∀ᶠ z in 𝓝 (0 : ℂ), F0 z = 0
  · left
    filter_upwards [hzero.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hi
    simpa only [F0, reflectedField, if_pos hi] using hz
  · right
    obtain ⟨m, g, hg, hg0, hfactor⟩ := exists_gauged_power_factor_off_real
      hR hB hA0m hA0s hA0b hsmall isOpen_ball (mem_ball_self hR)
      hA0C1 hF0 hF0C1 hF0eq hzero
    have hP := cauchyGauge_measurable_spec hR hB hA0m hA0s hA0b hsmall
    have hPg0 : cauchyGauge A0 0 (g 0) ≠ 0 := by
      intro hzero
      apply hg0
      have h := congrArg
        (fun v => (Ring.inverse (cauchyGauge A0 0) :
          (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) v) hzero
      change (Ring.inverse (cauchyGauge A0 0) * cauchyGauge A0 0) (g 0) = _ at h
      rw [Ring.inverse_mul_cancel _ (hP.2.2.2 0)] at h
      simpa using h
    have hcont : ContinuousAt (fun z => cauchyGauge A0 z (g z)) 0 :=
      hP.1.continuousAt.clm_apply hg.continuousAt
    refine ⟨m, g, hg, hg0, hPg0, hcont, ?_⟩
    filter_upwards [hfactor.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hi
    simpa only [F0, reflectedField, if_pos hi] using hz

end PoincareConjecture.M65Branch
