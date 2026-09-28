import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceInnerGeometry

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower

theorem exists_reference_high_critical_geometry :
    let U : E2 → ℝ := fun v =>
      ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
    let g : ℝ → ℝ := fun w => (2 - 1 / w) * Real.sqrt (1 - w ^ 2)
    ∃ ws wm : ℝ,
      1 / 2 < ws ∧ ws < 3 / 4 ∧ g ws = 1 / 32 ∧
      0 < wm ∧ wm < 1 / 2 ∧ g wm = -(1 / 32) ∧
      let vs : E2 := !₂[-Real.sqrt (1 - ws ^ 2), 0]
      let vm : E2 := !₂[Real.sqrt (1 - wm ^ 2), 0]
      let k : ℝ := U vs
      let mu : ℝ := U vm
      ‖vs‖ < 1 ∧ ‖vm‖ < 1 ∧
      (37 : ℝ) / 32 < k ∧ k < 5 / 4 ∧ 5 / 4 < mu ∧
      ContDiffOn ℝ ∞ U (Metric.ball 0 1) ∧
      fderiv ℝ U vm = 0 ∧
      (∀ v ∈ Metric.closedBall (0 : E2) 1, U v ≤ mu) ∧
      (∀ v ∈ Metric.closedBall (0 : E2) 1, U v = mu ↔ v = vm) ∧
      (∀ v ∈ Metric.ball (0 : E2) 1, (17 : ℝ) / 16 < U v →
        fderiv ℝ U v = 0 → v = vs ∨ v = vm) ∧
      (∀ w : E2, w ≠ 0 →
        0 < (fderiv ℝ (fderiv ℝ (fun v : E2 => -U v)) vm w) w) ∧
      Function.Injective (fderiv ℝ (fderiv ℝ (fun v : E2 => -U v)) vm) := by
  classical
  dsimp only
  let U : E2 → ℝ := fun v =>
    ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32
  let g : ℝ → ℝ := fun w => (2 - 1 / w) * Real.sqrt (1 - w ^ 2)
  let s : E2 → ℝ := fun v => Real.sqrt (1 - ‖v‖ ^ 2)
  let A : E2 → ℝ := fun v => 2 - 1 / s v
  let P : E2 →L[ℝ] ℝ := EuclideanSpace.proj 0
  let I : E2 →L[ℝ] E2 →L[ℝ] ℝ := (innerSL ℝ (E := E2)).toContinuousLinearMap
  have hNorm (v : E2) : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
    simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have hrad (v : E2) (hv : v ∈ ball (0 : E2) 1) : 0 < 1 - ‖v‖ ^ 2 := by
    rw [mem_ball_zero_iff] at hv
    nlinarith only [norm_nonneg v, hv]
  have hspos (v : E2) (hv : v ∈ ball (0 : E2) 1) : 0 < s v :=
    Real.sqrt_pos.mpr (hrad v hv)
  have hssq (v : E2) (hv : v ∈ ball (0 : E2) 1) :
      (s v) ^ 2 = 1 - ‖v‖ ^ 2 := Real.sq_sqrt (hrad v hv).le
  have hcont : Continuous U :=
    ((continuous_norm.pow 2).add
      (Real.continuous_sqrt.comp (continuous_const.sub (continuous_norm.pow 2)))).add
      (P.continuous.div_const 32)
  have hsmooth : ContDiffOn ℝ ∞ U (ball (0 : E2) 1) :=
    inner_reference_convex_geometry.1
  have hfirst (v : E2) (hv : v ∈ ball (0 : E2) 1) :
      HasFDerivAt U (A v • innerSL ℝ v + (1 / 32 : ℝ) • P) v := by
    have hsq := (hasStrictFDerivAt_norm_sq v).hasFDerivAt
    have hs := (hsq.const_sub (1 : ℝ)).sqrt (hrad v hv).ne'
    have hp := (P.hasFDerivAt (x := v)).const_smul (1 / 32 : ℝ)
    have hh := (hsq.add hs).add hp
    convert! hh using 1
    · ext y
      change _ = ‖y‖ ^ 2 + s y + (1 / 32 : ℝ) * y 0
      dsimp only [U, s]
      ring
    · ext w
      simp only [add_apply, smul_apply, neg_apply, smul_eq_mul, innerSL_apply_apply]
      dsimp only [A, s]
      field_simp [(hspos v hv).ne']
      ring
  have hsecond (v : E2) (hv : v ∈ ball (0 : E2) 1) :
      HasFDerivAt (fderiv ℝ U)
        (A v • I +
          ((-(1 / (s v) ^ 3)) • innerSL ℝ v).smulRight (innerSL ℝ v)) v := by
    have hscalar : HasDerivAt (fun r : ℝ => 2 - 1 / Real.sqrt (1 - r))
        (-1 / (2 * (s v) ^ 3)) (‖v‖ ^ 2) := by
      have hh := ((((hasDerivAt_id (‖v‖ ^ 2)).const_sub (1 : ℝ)).sqrt
        (hrad v hv).ne').inv (hspos v hv).ne').const_sub (2 : ℝ)
      convert! hh using 1
      · ext r
        simp only [one_div, Pi.inv_apply, id_eq]
      · dsimp only [s, id_eq]
        field_simp [(hspos v hv).ne']
    have ha : HasFDerivAt A (-(1 / (s v) ^ 3) • innerSL ℝ v) v := by
      convert! hscalar.comp_hasFDerivAt v
        (hasStrictFDerivAt_norm_sq v).hasFDerivAt using 1
      ext w
      simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]
      ring
    have hj := (ha.smul I.hasFDerivAt).add_const ((1 / 32 : ℝ) • P)
    apply hj.congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds hv] with y hy
    exact (hfirst y hy).fderiv
  have hcrit (v : E2) (hv : v ∈ ball (0 : E2) 1)
      (hc : fderiv ℝ U v = 0) :
      A v * v 0 = -(1 / 32 : ℝ) ∧ v 1 = 0 ∧ s v < 1 ∧ s v ≠ 1 / 2 := by
    have hh := hc
    rw [(hfirst v hv).fderiv] at hh
    have hx : A v * v 0 + (1 / 32 : ℝ) = 0 := by
      simpa [P, EuclideanSpace.inner_single_right] using
        congrArg (fun T : E2 →L[ℝ] ℝ => T (EuclideanSpace.single 0 1)) hh
    have hy : A v = 0 ∨ v 1 = 0 := by
      simpa [P, EuclideanSpace.inner_single_right] using
        congrArg (fun T : E2 →L[ℝ] ℝ => T (EuclideanSpace.single 1 1)) hh
    have hx' : A v * v 0 = -(1 / 32 : ℝ) := by linarith only [hx]
    have hA : A v ≠ 0 := by intro hz; rw [hz, zero_mul] at hx'; norm_num at hx'
    have hy' : v 1 = 0 := hy.resolve_left hA
    have hslt : s v < 1 := by
      have hh := hssq v hv
      have hn := hNorm v
      have hxne : v 0 ≠ 0 := by intro hz; rw [hz, mul_zero] at hx'; norm_num at hx'
      nlinarith only [hh, hn, hspos v hv, sq_pos_of_ne_zero hxne]
    refine ⟨hx', hy', hslt, ?_⟩
    intro hz
    apply hA
    dsimp only [A]
    rw [hz]
    norm_num
  obtain ⟨ws, hws, hwsunique⟩ := exists_unique_nestedReference_saddle_root
  obtain ⟨hws0, hws1, hwsroot⟩ := hws
  let vs : E2 := !₂[-Real.sqrt (1 - ws ^ 2), 0]
  have hwspos : 0 < ws := by linarith only [hws0]
  have hwssq : 0 < 1 - ws ^ 2 := by nlinarith only [hws0, hws1]
  have hvssq : ‖vs‖ ^ 2 = 1 - ws ^ 2 := by
    rw [hNorm]
    change (-Real.sqrt (1 - ws ^ 2)) ^ 2 + (0 : ℝ) ^ 2 = _
    rw [neg_sq, Real.sq_sqrt hwssq.le]
    ring
  have hvs : ‖vs‖ < 1 := by
    nlinarith only [hvssq, sq_pos_of_pos hwspos, norm_nonneg vs]
  have hvss : s vs = ws := by
    dsimp only [s]
    rw [hvssq, sub_sub_cancel, Real.sqrt_sq_eq_abs, abs_of_pos hwspos]
  have hUvs : U vs = 1 - ws ^ 2 + ws - Real.sqrt (1 - ws ^ 2) / 32 := by
    change ‖vs‖ ^ 2 + s vs + (-Real.sqrt (1 - ws ^ 2)) / 32 = _
    rw [hvssq, hvss]
    ring
  have hks : (37 : ℝ) / 32 < U vs ∧ U vs < 5 / 4 := by
    have hr0 := Real.sqrt_pos.mpr hwssq
    have hr1 : Real.sqrt (1 - ws ^ 2) < 1 := by
      nlinarith only [Real.sq_sqrt hwssq.le, Real.sqrt_nonneg (1 - ws ^ 2),
        sq_pos_of_pos hwspos]
    have hp := mul_pos (sub_pos.mpr hws1) (show 0 < ws - 1 / 4 by linarith only [hws0])
    rw [hUvs]
    constructor
    · nlinarith only [hp, hr1]
    · nlinarith only [sq_nonneg (ws - 1 / 2), hr0]
  have hclass (v : E2) (hv : v ∈ ball (0 : E2) 1)
      (hh : (17 : ℝ) / 16 < U v) (hc : fderiv ℝ U v = 0) :
      v = vs ∨ (0 < s v ∧ s v < 1 / 2 ∧ g (s v) = -(1 / 32) ∧
        v = (!₂[Real.sqrt (1 - (s v) ^ 2), 0] : E2)) := by
    obtain ⟨hx, hy, hw1, hwhalf⟩ := hcrit v hv hc
    have hw0 := hspos v hv
    have hvw : (v 0) ^ 2 + (s v) ^ 2 = 1 := by
      have hs := hssq v hv
      rw [hNorm, hy, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] at hs
      linarith only [hs]
    have hlinear : (2 * s v - 1) * v 0 = -(s v / 32) := by
      have hx' := hx
      dsimp only [A] at hx'
      apply (mul_left_cancel₀ (show (32 : ℝ) ≠ 0 by norm_num))
      have halg : s v * ((2 - 1 / s v) * v 0) = (2 * s v - 1) * v 0 := by
        field_simp [hw0.ne']
      rw [← halg, hx']
      ring
    have hheight : s v * (U v - 1) = (s v - 1) * ((s v) ^ 2 + s v - 1) := by
      have hmul := congrArg (fun z : ℝ => z * v 0) hlinear
      have hsphere := congrArg (fun z : ℝ => s v * z) hvw
      change s v * (‖v‖ ^ 2 + s v + v 0 / 32 - 1) = _
      rw [hNorm, hy, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
      nlinarith only [hmul, hsphere, hvw]
    have hwupper : s v < 3 / 4 := by
      by_contra hn
      have hn' : 3 / 4 ≤ s v := le_of_not_gt hn
      have hp : 0 ≤ (s v) ^ 2 + s v - 1 := by
        nlinarith only [hn', sq_nonneg (s v - 3 / 4)]
      have hnonpos := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hw1.le) hp
      have hpos := mul_pos hw0 (show 0 < U v - 1 by linarith only [hh])
      linarith only [hheight, hnonpos, hpos]
    have hr0 := Real.sqrt_nonneg (1 - (s v) ^ 2)
    have hr2 : (Real.sqrt (1 - (s v) ^ 2)) ^ 2 = (v 0) ^ 2 := by
      rw [Real.sq_sqrt (by nlinarith only [hvw, sq_nonneg (v 0)])]
      linarith only [hvw]
    rcases lt_or_gt_of_ne hwhalf with hwsmall | hwlarge
    · right
      have hAneg : A v < 0 := by
        dsimp only [A]
        have hi : (2 : ℝ) < 1 / s v := (lt_div_iff₀ hw0).mpr (by linarith only [hwsmall])
        linarith only [hi]
      have hxpos : 0 < v 0 := by nlinarith only [hx, hAneg]
      have hxeq : v 0 = Real.sqrt (1 - (s v) ^ 2) := by
        nlinarith only [hr0, hr2, hxpos]
      refine ⟨hw0, hwsmall, ?_, ?_⟩
      · change A v * Real.sqrt (1 - (s v) ^ 2) = _
        rwa [← hxeq]
      · ext i
        fin_cases i
        · exact hxeq
        · exact hy
    · left
      have hApos : 0 < A v := by
        dsimp only [A]
        have hi : 1 / s v < (2 : ℝ) := (div_lt_iff₀ hw0).mpr (by linarith only [hwlarge])
        linarith only [hi]
      have hxneg : v 0 < 0 := by nlinarith only [hx, hApos]
      have hxeq : v 0 = -Real.sqrt (1 - (s v) ^ 2) := by
        nlinarith only [hr0, hr2, hxneg]
      have hgroot : g (s v) = (1 / 32 : ℝ) := by
        change A v * Real.sqrt (1 - (s v) ^ 2) = _
        rw [hxeq] at hx
        nlinarith only [hx]
      have he : s v = ws := hwsunique (s v) ⟨hwlarge, hwupper, hgroot⟩
      ext i
      fin_cases i
      · change v 0 = -Real.sqrt (1 - ws ^ 2)
        simpa only [he] using hxeq
      · exact hy
  have hgder (w : ℝ) (hw : w ∈ Ioo (0 : ℝ) (1 / 2)) :
      HasDerivAt g ((1 - 2 * w ^ 3) / (w ^ 2 * Real.sqrt (1 - w ^ 2))) w ∧
        0 < (1 - 2 * w ^ 3) / (w ^ 2 * Real.sqrt (1 - w ^ 2)) := by
    have hrad0 : 0 < 1 - w ^ 2 := by nlinarith only [hw.1, hw.2]
    have hcube := pow_le_pow_left₀ hw.1.le hw.2.le 3
    norm_num at hcube
    let r : ℝ := Real.sqrt (1 - w ^ 2)
    have hr0 : 0 < r := Real.sqrt_pos.mpr hrad0
    have hr2 : r ^ 2 = 1 - w ^ 2 := Real.sq_sqrt hrad0.le
    have hinv : HasDerivAt (fun x : ℝ => x⁻¹) (-1 / w ^ 2) w :=
      (hasDerivAt_id w).inv hw.1.ne'
    have ha : HasDerivAt (fun x : ℝ => 2 - 1 / x) (1 / w ^ 2) w := by
      simpa only [one_div, neg_div, neg_neg] using hinv.const_sub (2 : ℝ)
    have hradder : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * w) w := by
      simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
        pow_one, mul_one, neg_mul] using ((hasDerivAt_id w).pow 2).const_sub (1 : ℝ)
    have hh : HasDerivAt g
        ((1 / w ^ 2) * r + (2 - 1 / w) * ((-2 * w) / (2 * r))) w :=
      ha.mul (hradder.sqrt hrad0.ne')
    have halg : (1 / w ^ 2) * r + (2 - 1 / w) * ((-2 * w) / (2 * r)) =
        (1 - 2 * w ^ 3) / (w ^ 2 * r) := by
      calc
        _ = r ^ 2 / (w ^ 2 * r) + (w ^ 2 - 2 * w ^ 3) / (w ^ 2 * r) := by
          congr 1
          · field_simp [hw.1.ne', hr0.ne']
          · field_simp [hw.1.ne', hr0.ne']
            ring
        _ = (1 - 2 * w ^ 3) / (w ^ 2 * r) := by
          rw [← add_div]
          congr 1
          nlinarith only [hr2]
    rw [halg] at hh
    exact ⟨hh, div_pos (by linarith only [hcube]) (mul_pos (sq_pos_of_pos hw.1) hr0)⟩
  have hgmono : StrictMonoOn g (Ioo (0 : ℝ) (1 / 2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
      (fun w hw => (hgder w hw).1.continuousAt.continuousWithinAt)
    intro w hw
    obtain ⟨hd, hp⟩ := hgder w (interior_subset hw)
    rw [hd.deriv]
    exact hp
  let vt : E2 := !₂[Real.sqrt 3 / 2, 0]
  have hvtsq : ‖vt‖ ^ 2 = 3 / 4 := by
    rw [hNorm]
    change (Real.sqrt 3 / 2) ^ 2 + (0 : ℝ) ^ 2 = _
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  have hvt : vt ∈ closedBall (0 : E2) 1 := mem_closedBall_zero_iff.mpr (by
    nlinarith only [hvtsq, norm_nonneg vt])
  have hUt : (5 : ℝ) / 4 < U vt := by
    have hs : s vt = 1 / 2 := by
      have hsq : s vt ^ 2 = 1 / 4 := by
        dsimp only [s]
        rw [hvtsq, Real.sq_sqrt (by norm_num)]
        norm_num
      have hn : 0 ≤ s vt := Real.sqrt_nonneg _
      nlinarith only [hsq, hn]
    have hp := Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)
    change _ < ‖vt‖ ^ 2 + s vt + (Real.sqrt 3 / 2) / 32
    rw [hvtsq, hs]
    linarith only [hp]
  have hboundary (v : E2) (hv : ‖v‖ = 1) : U v ≤ 33 / 32 := by
    have hc : v 0 ≤ 1 := (le_abs_self _).trans (hv ▸ PiLp.norm_apply_le v 0)
    change ‖v‖ ^ 2 + Real.sqrt (1 - ‖v‖ ^ 2) + v 0 / 32 ≤ _
    rw [hv]
    norm_num
    linarith only [hc]
  obtain ⟨vstar, hvstar, hmax⟩ := (isCompact_closedBall (0 : E2) 1).exists_isMaxOn
    ⟨vt, hvt⟩ hcont.continuousOn
  have hmaxhigh : (5 : ℝ) / 4 < U vstar := hUt.trans_le (hmax hvt)
  have hhighInterior (v : E2) (hv : v ∈ closedBall (0 : E2) 1)
      (hh : (5 : ℝ) / 4 < U v) : v ∈ ball (0 : E2) 1 := by
    rw [mem_ball_zero_iff]
    rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hv) with hn | hn
    · exact hn
    · have hb := hboundary v hn
      linarith only [hb, hh]
  have hvstarOpen := hhighInterior vstar hvstar hmaxhigh
  have hmaxcrit : fderiv ℝ U vstar = 0 :=
    (hmax.isLocalMax (mem_of_superset (isOpen_ball.mem_nhds hvstarOpen)
      ball_subset_closedBall)).fderiv_eq_zero
  have hstarclass := hclass vstar hvstarOpen (by linarith only [hmaxhigh]) hmaxcrit
  have hstar : 0 < s vstar ∧ s vstar < 1 / 2 ∧ g (s vstar) = -(1 / 32) ∧
      vstar = (!₂[Real.sqrt (1 - (s vstar) ^ 2), 0] : E2) := by
    rcases hstarclass with hs | hs
    · rw [hs] at hmaxhigh
      linarith only [hmaxhigh, hks.2]
    · exact hs
  let wm := s vstar
  let vm : E2 := !₂[Real.sqrt (1 - wm ^ 2), 0]
  have hvstarEq : vstar = vm := hstar.2.2.2
  have hwm : 0 < wm ∧ wm < 1 / 2 := ⟨hstar.1, hstar.2.1⟩
  have hvm : vm ∈ ball (0 : E2) 1 := hvstarEq ▸ hvstarOpen
  have hsm : s vm = wm := congrArg s hvstarEq.symm
  have hvmcrit : fderiv ℝ U vm = 0 := hvstarEq ▸ hmaxcrit
  have hvmhigh : (5 : ℝ) / 4 < U vm := hvstarEq ▸ hmaxhigh
  have hvmmax (v : E2) (hv : v ∈ closedBall (0 : E2) 1) : U v ≤ U vm :=
    hvstarEq ▸ hmax hv
  have hhighclass (v : E2) (hv : v ∈ ball (0 : E2) 1)
      (hh : (17 : ℝ) / 16 < U v) (hc : fderiv ℝ U v = 0) : v = vs ∨ v = vm := by
    rcases hclass v hv hh hc with hvs | hvp
    · exact Or.inl hvs
    · right
      have he : s v = wm := hgmono.injOn ⟨hvp.1, hvp.2.1⟩ hwm
        (hvp.2.2.1.trans hstar.2.2.1.symm)
      simpa only [he, vm] using hvp.2.2.2
  have hvmunique (v : E2) (hv : v ∈ closedBall (0 : E2) 1) : U v = U vm ↔ v = vm := by
    constructor
    · intro he
      have hh : (5 : ℝ) / 4 < U v := he.symm ▸ hvmhigh
      have hvo := hhighInterior v hv hh
      have hvmax : IsMaxOn U (closedBall (0 : E2) 1) v := by
        intro x hx
        rw [he]
        exact hvmmax x hx
      have hc := (hvmax.isLocalMax (mem_of_superset (isOpen_ball.mem_nhds hvo)
        ball_subset_closedBall)).fderiv_eq_zero
      rcases hhighclass v hvo (by linarith only [hh]) hc with hs | hs
      · rw [hs] at hh
        linarith only [hh, hks.2]
      · exact hs
    · rintro rfl
      rfl

  have hnegsecond : HasFDerivAt (fderiv ℝ (fun v : E2 => -U v))
      (-(A vm • I +
        ((-(1 / (s vm) ^ 3)) • innerSL ℝ vm).smulRight (innerSL ℝ vm))) vm := by
    apply (hsecond vm hvm).neg.congr_of_eventuallyEq
    filter_upwards [isOpen_ball.mem_nhds hvm] with v hv
    change fderiv ℝ (-U) v = -fderiv ℝ U v
    rw [(hfirst v hv).neg.fderiv, (hfirst v hv).fderiv]
  have hnegative : A vm < 0 := by
    dsimp only [A]
    rw [hsm]
    have hi : (2 : ℝ) < 1 / wm := (lt_div_iff₀ hwm.1).mpr (by linarith only [hwm.2])
    linarith only [hi]
  have hpositive (w : E2) (hw : w ≠ 0) :
      0 < (fderiv ℝ (fderiv ℝ (fun v : E2 => -U v)) vm w) w := by
    rw [hnegsecond.fderiv]
    change 0 < -(A vm * ⟪w, w⟫_ℝ +
      (-(1 / (s vm) ^ 3) * ⟪vm, w⟫_ℝ) * ⟪vm, w⟫_ℝ)
    rw [real_inner_self_eq_norm_sq]
    have hp := mul_neg_of_neg_of_pos hnegative (sq_pos_of_pos (norm_pos_iff.mpr hw))
    have hnonneg : 0 ≤ ⟪vm, w⟫_ℝ ^ 2 / (s vm) ^ 3 :=
      div_nonneg (sq_nonneg _) (pow_pos (hspos vm hvm) 3).le
    calc
      0 < -(A vm * ‖w‖ ^ 2) + ⟪vm, w⟫_ℝ ^ 2 / (s vm) ^ 3 :=
        add_pos_of_pos_of_nonneg (neg_pos.mpr hp) hnonneg
      _ = _ := by ring
  refine ⟨ws, wm, hws0, hws1, hwsroot, hwm.1, hwm.2, hstar.2.2.1,
    hvs, mem_ball_zero_iff.mp hvm, hks.1, hks.2, hvmhigh, hsmooth, hvmcrit,
    hvmmax, hvmunique, hhighclass, hpositive, ?_⟩
  intro x y hxy
  by_contra hn
  have hh := hpositive (x - y) (sub_ne_zero.mpr hn)
  have he : fderiv ℝ (fderiv ℝ (fun v : E2 => -U v)) vm (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  rw [he, zero_apply] at hh
  exact (lt_irrefl (0 : ℝ)) hh

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
