import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchWeakCRRegularity
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchWeakCRMultiplier

set_option autoImplicit false

open Set Metric Filter MeasureTheory Complex
open scoped Topology ContDiff SchwartzMap Convolution

namespace PoincareConjecture.M65Boundary

open M65Branch

private theorem cauchy_reproducer {chi : ℂ → ℂ}
    (hc : ContDiff ℝ ∞ chi) (hs : HasCompactSupport chi)
    (hone : chi =ᶠ[𝓝 (0 : ℂ)] fun _ => 1) :
    ∃ k : ℂ → ℂ, ContDiff ℝ ∞ k ∧ HasCompactSupport k ∧
      tsupport k ⊆ tsupport chi ∧
      ∀ (G : ℂ → ℂ), ContDiff ℝ ∞ G →
        (∀ z ∈ tsupport chi, dbar G z = 0) →
        (∫ z, k z * G z) = G 0 := by
  let k (z : ℂ) := -(Real.pi : ℂ)⁻¹ * (z⁻¹ * dbar chi z)
  have hd : ContDiff ℝ ∞ (dbar chi) :=
    dbarLinear.contDiff.comp (hc.fderiv_right (by simp))
  have hd0 : dbar chi =ᶠ[𝓝 (0 : ℂ)] fun _ => 0 := by
    filter_upwards [hone.fderiv (𝕜 := ℝ)] with z hz
    simp only [dbar, hz, fderiv_const_apply, map_zero]
  have hk : ContDiff ℝ ∞ k := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z = 0
    · subst z
      refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [hd0] with w hw
      change -(Real.pi : ℂ)⁻¹ * (w⁻¹ * dbar chi w) = 0
      rw [hw, mul_zero, mul_zero]
    · exact contDiffAt_const.mul ((contDiffAt_id.inv hz).mul hd.contDiffAt)
  have hsub : tsupport k ⊆ tsupport chi := by
    apply closure_minimal ?_ (isClosed_tsupport _)
    intro z hz
    by_contra hnot
    have hdzero : dbar chi z = 0 := by
      change dbarLinear (fderiv ℝ chi z) = 0
      rw [fderiv_of_notMem_tsupport ℝ hnot, map_zero]
    exact hz (by simp only [k, hdzero, mul_zero])
  refine ⟨k, hk, hs.of_isClosed_subset (isClosed_tsupport _) hsub, hsub, ?_⟩
  intro G hG hbar
  have hp (z : ℂ) : dbar (fun w => chi w * G w) z = dbar chi z * G z := by
    rw [dbar_mul (hc.differentiable (by simp) z) (hG.differentiable (by simp) z)]
    by_cases hz : z ∈ tsupport chi
    · rw [hbar z hz, mul_zero, add_zero]
    · rw [image_eq_zero_of_notMem_tsupport hz, zero_mul, add_zero]
  have hi := integral_inv_smul_dbar ((hc.mul hG).of_le (by simp)) hs.mul_right
  have hχ0 : chi 0 = 1 := hone.eq_of_nhds
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  calc
    (∫ z, k z * G z) = -(Real.pi : ℂ)⁻¹ *
        (∫ z : ℂ, z⁻¹ • dbar (fun w => chi w * G w) z) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [hp, smul_eq_mul, k, mul_assoc]
    _ = G 0 := by
      rw [hi.2, hχ0, one_mul, smul_eq_mul]
      field_simp

private theorem smooth_convolution_commute {k j F : ℂ → ℂ}
    (hk : Continuous k) (hks : HasCompactSupport k)
    (hj : Continuous j) (hjs : HasCompactSupport j)
    (hF : Integrable F volume) :
    k ⋆[ContinuousLinearMap.mul ℝ ℂ, volume]
        (j ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] F) =
      j ⋆[ContinuousLinearMap.mul ℝ ℂ, volume]
        (k ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] F) := by
  let L := ContinuousLinearMap.mul ℝ ℂ
  let LR := ContinuousLinearMap.mul ℝ ℝ
  have assoc (a b : ℂ → ℂ) (ha : Continuous a) (has : HasCompactSupport a)
      (hb : Continuous b) (hbs : HasCompactSupport b) (x : ℂ) :
      ((a ⋆[L, volume] b) ⋆[L, volume] F) x =
        (a ⋆[L, volume] (b ⋆[L, volume] F)) x := by
    have hai : Integrable a volume := ha.integrable_of_hasCompactSupport has
    have hbi : Integrable b volume := hb.integrable_of_hasCompactSupport hbs
    apply convolution_assoc L L L L (fun _ _ _ => mul_assoc _ _ _)
      ha.aestronglyMeasurable hb.aestronglyMeasurable hF.aestronglyMeasurable
      (hai.ae_convolution_exists L hbi) (hbi.norm.ae_convolution_exists LR hF.norm)
    exact has.norm.convolutionExists_left LR ha.norm
      (hbi.norm.integrable_convolution LR hF.norm).locallyIntegrable x
  have hcomm : k ⋆[L, volume] j = j ⋆[L, volume] k := by
    have hflip : L.flip = L := by
      ext a b
      exact mul_comm b a
    rw [← convolution_flip L, hflip]
  funext x
  rw [← assoc k j hk hks hj hjs x, hcomm, assoc j k hj hjs hk hks x]

set_option maxHeartbeats 1200000 in

theorem exists_holomorphic_representative {F : ℂ → ℂ} {U : Set ℂ}
    (hF : Integrable F volume) (hU : IsOpen U)
    (hweak : ∀ ψ : 𝓢(ℂ, ℂ), HasCompactSupport (ψ : ℂ → ℂ) →
      tsupport (ψ : ℂ → ℂ) ⊆ U → (∫ w, dbar ψ w * F w) = 0)
    {x : ℂ} (hx : x ∈ U) :
    ∃ r > 0, ∃ H : ℂ → ℂ, ContDiff ℝ ∞ H ∧
      DifferentiableOn ℂ H (ball x r) ∧ F =ᵐ[volume.restrict (ball x r)] H := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hquarter : 0 < r / 4 := by positivity
  let χ : ContDiffBump (0 : ℂ) :=
    { rIn := r / 8
      rOut := r / 4
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let chi (z : ℂ) : ℂ := χ z
  have hc : ContDiff ℝ ∞ chi := ofRealCLM.contDiff.comp χ.contDiff
  have hcs : HasCompactSupport chi :=
    χ.hasCompactSupport.comp_left (g := fun a : ℝ => (a : ℂ)) ofReal_zero
  have hc1 : chi =ᶠ[𝓝 (0 : ℂ)] fun _ => 1 := by
    filter_upwards [χ.eventuallyEq_one] with z hz
    change (χ z : ℂ) = 1
    rw [hz]
    simp
  have hcsub : tsupport chi ⊆ closedBall (0 : ℂ) (r / 4) := by
    apply closure_minimal ?_ isClosed_closedBall
    intro z hz
    have hχ : z ∈ Function.support (χ : ℂ → ℝ) := by
      intro hz0
      exact hz (by simp only [chi, hz0, ofReal_zero])
    rw [χ.support_eq] at hχ
    exact ball_subset_closedBall hχ
  obtain ⟨k, hk, hks, _hksub, hrepro⟩ := cauchy_reproducer hc hcs hc1
  let L := ContinuousLinearMap.mul ℝ ℂ
  let H : ℂ → ℂ := k ⋆[L, volume] F
  have hH : ContDiff ℝ ∞ H := hks.contDiff_convolution_left L hk hF.locallyIntegrable
  let δ (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp only [δ]; positivity
  have hδ0 : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let φ (n : ℕ) : ContDiffBump (0 : ℂ) :=
    { rIn := δ n / 3
      rOut := δ n
      rIn_pos := div_pos (hδ n) (by norm_num)
      rIn_lt_rOut := by linarith [hδ n] }
  let j (n : ℕ) (z : ℂ) : ℂ := (φ n).normed volume z
  let f (n : ℕ) : ℂ → ℂ := j n ⋆[L, volume] F
  have hj (n : ℕ) : ContDiff ℝ ∞ (j n) :=
    ofRealCLM.contDiff.comp (φ n).contDiff_normed
  have hjs (n : ℕ) : HasCompactSupport (j n) :=
    (φ n).hasCompactSupport_normed.comp_left (g := fun a : ℝ => (a : ℂ)) ofReal_zero
  have hjsub (n : ℕ) : tsupport (j n) ⊆ closedBall (0 : ℂ) (δ n) := by
    apply closure_minimal ?_ isClosed_closedBall
    intro z hz
    have hz' : z ∈ Function.support ((φ n).normed volume) := by
      intro hz0
      exact hz (by simp only [j, hz0, ofReal_zero])
    rw [(φ n).support_normed_eq] at hz'
    exact ball_subset_closedBall hz'
  have hsame (n : ℕ) (G : ℂ → ℂ) :
      (j n ⋆[L, volume] G) =
        (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G := by
    funext z
    apply integral_congr_ae
    filter_upwards [] with w
    simp only [ContinuousLinearMap.mul_apply', ContinuousLinearMap.lsmul_apply, j,
      real_smul, L]
  have hf (n : ℕ) : ContDiff ℝ ∞ (f n) :=
    (hjs n).contDiff_convolution_left L (hj n) hF.locallyIntegrable
  have hsmall : ∀ᶠ n in atTop, δ n < r / 4 := hδ0.eventually (gt_mem_nhds hquarter)
  have hrep (y : ℂ) (hy : y ∈ ball x (r / 4)) :
      ∀ᶠ n in atTop, (k ⋆[L, volume] f n) y = f n y := by
    filter_upwards [hsmall] with n hn
    let G (z : ℂ) := f n (y - z)
    have hG : ContDiff ℝ ∞ G := (hf n).comp (contDiff_const.sub contDiff_id)
    have hbar (z : ℂ) (hz : z ∈ tsupport chi) : dbar G z = 0 := by
      have hfn : dbar (f n) (y - z) = 0 := by
        apply dbar_convolution_eq_zero_of_weak (hj n) (hjs n) hF.locallyIntegrable
          hweak (y - z)
        intro w hw
        apply hsub
        have hwz : dist w (y - z) ≤ δ n := by
          have he := mem_closedBall_zero_iff.mp (hjsub n hw)
          simpa only [dist_eq_norm, norm_sub_rev] using he
        have hzy : dist (y - z) y ≤ r / 4 := by
          simpa only [dist_eq_norm, sub_sub_cancel_left, norm_neg] using
            mem_closedBall_zero_iff.mp (hcsub hz)
        have hy' := mem_ball.mp hy
        exact mem_ball.mpr ((dist_triangle w (y - z) x).trans_lt (by
          have ht := dist_triangle (y - z) y x
          linarith))
      have hd := ((hf n).differentiable (by simp) (y - z)).hasFDerivAt.comp z
        ((hasFDerivAt_const y z).sub (hasFDerivAt_id z))
      change HasFDerivAt G _ z at hd
      have he : dbar G z = -dbar (f n) (y - z) := by
        simp only [dbar, hd.fderiv, dbarLinear, smul_apply, add_apply,
          ContinuousLinearMap.apply_apply, ContinuousLinearMap.comp_apply,
          zero_sub, neg_apply, ContinuousLinearMap.id_apply, map_neg, smul_eq_mul]
        ring
      rw [he, hfn, neg_zero]
    have he := hrepro G hG hbar
    change (∫ z, k z * f n (y - z)) = f n y
    simpa only [G, sub_zero] using he
  have hlim : ∀ᵐ y ∂volume, Tendsto (fun n => f n y) atTop (𝓝 (F y)) := by
    have hratio : ∀ᶠ n in atTop, (φ n).rOut ≤ 3 * (φ n).rIn :=
      Eventually.of_forall fun n => by change δ n ≤ 3 * (δ n / 3); linarith
    have hh := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (φ := φ) hδ0 hratio hF.locallyIntegrable
    simpa only [f, hsame] using hh
  have hlimH : ∀ y : ℂ, Tendsto (fun n => (j n ⋆[L, volume] H) y) atTop (𝓝 (H y)) := by
    intro y
    have hh := tendstoLocallyUniformlyOn_bump_convolution
      hH.continuous.locallyIntegrable isOpen_univ hH.continuous.continuousOn φ hδ0
    simpa only [hsame] using hh.tendsto_at (mem_univ y)
  have heq : F =ᵐ[volume.restrict (ball x (r / 4))] H := by
    filter_upwards [ae_restrict_of_ae hlim, ae_restrict_mem measurableSet_ball] with y hy hyball
    have hHlim := hlimH y
    have hfnlim : Tendsto (fun n => f n y) atTop (𝓝 (H y)) := by
      apply hHlim.congr'
      filter_upwards [hrep y hyball] with n hn
      have hcomm := congrFun (smooth_convolution_commute hk.continuous hks
        (hj n).continuous (hjs n) hF) y
      exact hcomm.symm.trans hn
    exact tendsto_nhds_unique hy hfnlim
  refine ⟨r / 4, hquarter, H, hH, ?_, heq⟩
  apply differentiableOn_of_weak_dbar_eq_zero hH.continuous.locallyIntegrable
    isOpen_ball hH.continuous.continuousOn
  intro ψ hψ hψsub
  have hballU : ball x (r / 4) ⊆ U :=
    (ball_subset_ball (by linarith)).trans hsub
  have htest := hweak ψ hψ (hψsub.trans hballU)
  rw [← htest]
  apply integral_congr_ae
  have heq' : ∀ᵐ z ∂volume, z ∈ ball x (r / 4) → F z = H z :=
    (ae_restrict_iff' measurableSet_ball).mp heq
  filter_upwards [heq'] with z hz
  by_cases hzb : z ∈ ball x (r / 4)
  · rw [hz hzb]
  · have hdψ : dbar ψ z = 0 := by
      change dbarLinear (fderiv ℝ ψ z) = 0
      rw [fderiv_of_notMem_tsupport ℝ (fun h => hzb (hψsub h)), map_zero]
    rw [hdψ, zero_mul, zero_mul]

end PoincareConjecture.M65Boundary
