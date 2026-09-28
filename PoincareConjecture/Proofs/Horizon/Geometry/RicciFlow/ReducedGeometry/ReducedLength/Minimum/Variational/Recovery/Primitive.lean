import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.WeakH1
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Calculus.BumpFunction.Normed












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology
open scoped intervalIntegral ContDiff ENNReal

namespace PoincareConjecture.ReducedLengthMinimum.Variational

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem intervalL2_smooth_support_approx {a b : ℝ} (w : IntervalL2 E a b)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ q : ℝ → E, ContDiff ℝ ∞ q ∧ HasCompactSupport q ∧
      tsupport q ⊆ Ioo a b ∧ MemLp q 2 (volume.restrict (Icc a b)) ∧
      eLpNorm ((w : ℝ → E) - q) 2 (volume.restrict (Icc a b)) ≤ ε := by
  let U := Ioo a b
  let μ := volume.restrict (Icc a b)
  let ν : Measure U := volume.comap (Subtype.val : U → ℝ)
  let : LocallyCompactSpace U := isOpen_Ioo.locallyCompactSpace
  let : ν.Regular := Measure.Regular.comap' volume isOpen_Ioo.isOpenEmbedding_subtypeVal
  have he : MeasurableEmbedding (Subtype.val : U → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ioo
  have hmap : ν.map (Subtype.val : U → ℝ) = μ := by
    dsimp only [ν, μ, U]
    rw [map_comap_subtype_coe measurableSet_Ioo, restrict_Ioo_eq_restrict_Icc]
  have hw : MemLp (fun x : U ↦ w x) 2 ν := by
    apply he.memLp_map_measure_iff.mp
    rw [hmap]
    exact Lp.memLp w
  have hhalf : ε / 2 ≠ 0 := by simpa using hε
  obtain ⟨g, hgcompact, hgerror, hgcont, hgLp⟩ :=
    hw.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) hhalf
  let H : ℝ → E := (Subtype.val : U → ℝ).extend g 0
  have hHcont : Continuous H :=
    HasCompactSupport.continuous_extend_zero isOpen_Ioo hgcont hgcompact
  have hHcompact : HasCompactSupport H := hgcompact.extend_zero continuous_subtype_val
  have hHsrc : tsupport H ⊆ Ioo a b :=
    (hgcompact.tsupport_extend_zero_subset continuous_subtype_val).trans
      (Subtype.coe_image_subset _ _)
  have hHerror : eLpNorm ((w : ℝ → E) - H) 2 μ ≤ ε / 2 := by
    rw [← hmap, he.eLpNorm_map_measure]
    convert hgerror using 1
    congr 1
    funext x
    simp only [H, Function.comp_def, Pi.sub_apply,
      Subtype.val_injective.extend_apply]
  have hfinite : μ univ ^ (1 / (2 : ℝ≥0∞).toReal) ≠ (⊤ : ℝ≥0∞) := by
    apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
    exact measure_ne_top _ _
  obtain ⟨δ, hδ, hδbound⟩ := ENNReal.exists_nnreal_pos_mul_lt hfinite hhalf
  obtain ⟨q, hq, hqclose, hqsupp⟩ := hHcont.exists_contDiff_approx ⊤
    (ε := fun _ ↦ (δ : ℝ)) continuous_const (fun _ ↦ hδ)
  have hqcompact : HasCompactSupport q := hHcompact.mono hqsupp
  have hqLp : MemLp q 2 μ := hq.continuous.memLp_of_hasCompactSupport hqcompact
  have hsmooth : eLpNorm (H - q) 2 μ ≤ ε / 2 := by
    apply le_trans (eLpNorm_sub_le_of_dist_bdd μ (by norm_num) MeasurableSet.univ
      (show (0 : ℝ) ≤ δ from δ.coe_nonneg)
      (fun x ↦ by simpa only [dist_comm] using (hqclose x).le)
      (subset_univ _) (subset_univ _))
    simpa only [ENNReal.ofReal_coe_nnreal] using hδbound.le
  refine ⟨q, hq, hqcompact, (closure_mono hqsupp).trans hHsrc, hqLp, ?_⟩
  have hsum : (w : ℝ → E) - q = ((w : ℝ → E) - H) + (H - q) := by
    abel
  rw [hsum]
  apply (eLpNorm_add_le ((Lp.memLp w).aestronglyMeasurable.sub
      hHcont.aestronglyMeasurable) (hHcont.aestronglyMeasurable.sub
      hq.continuous.aestronglyMeasurable) (by norm_num)).trans
  simpa only [ENNReal.add_halves] using add_le_add hHerror hsmooth

omit [CompleteSpace E] in
theorem intervalL2_smooth_support_sequence {a b : ℝ} (w : IntervalL2 E a b) :
    ∃ (q : ℕ → ℝ → E) (hqLp : ∀ k, MemLp (q k) 2 (volume.restrict (Icc a b))),
      (∀ k, ContDiff ℝ ∞ (q k) ∧ HasCompactSupport (q k) ∧ tsupport (q k) ⊆ Ioo a b) ∧
      Tendsto (fun k ↦ (hqLp k).toLp (q k)) atTop (𝓝 w) := by
  have he (k : ℕ) : 0 < (1 / ((k : ℝ) + 1)) := by positivity
  choose q hq hqc hqs hqLp herror using fun k : ℕ ↦
    intervalL2_smooth_support_approx w (ENNReal.ofReal_ne_zero_iff.mpr (he k))
  refine ⟨q, hqLp, fun k ↦ ⟨hq k, hqc k, hqs k⟩, ?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsmall : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < ε :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hε)
  filter_upwards [hsmall] with k hk
  apply lt_of_le_of_lt _ hk
  rw [dist_comm, Lp.dist_def]
  have heq : eLpNorm ((w : ℝ → E) - ((hqLp k).toLp (q k) : ℝ → E)) 2
      (volume.restrict (Icc a b)) =
      eLpNorm ((w : ℝ → E) - q k) 2 (volume.restrict (Icc a b)) := by
    apply eLpNorm_congr_ae
    exact Filter.EventuallyEq.sub Filter.EventuallyEq.rfl (hqLp k).coeFn_toLp
  rw [heq]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (herror k)).trans_eq
    (ENNReal.toReal_ofReal (he k).le)

noncomputable def intervalL2_integral {a b : ℝ} : IntervalL2 E a b →L[ℝ] E :=
  (ContinuousLinearMap.lsmul ℝ ℝ (E := E)).lpPairing (volume.restrict (Icc a b)) 2 2
    (Lp.const 2 (volume.restrict (Icc a b)) (1 : ℝ))

theorem intervalL2_integral_apply {a b : ℝ} (hab : a ≤ b) (w : IntervalL2 E a b) :
    intervalL2_integral w = ∫ s in a..b, w s := by
  rw [intervalL2_integral, ContinuousLinearMap.lpPairing_eq_integral,
    intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const (p := (2 : ℝ≥0∞))
    (μ := volume.restrict (Icc a b)) (c := (1 : ℝ))] with s hs
  simp only [ContinuousLinearMap.lsmul_apply, hs, Function.const_apply, one_smul]

theorem exists_interior_normalized_bump {a b : ℝ} (hab : a < b) :
    ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
      tsupport β ⊆ Ioo a b ∧ (∫ s in a..b, β s) = 1 := by
  let c : ℝ := (a + b) / 2
  let f : ContDiffBump c := ⟨(b - a) / 8, (b - a) / 4, by linarith, by linarith⟩
  have hsupp : tsupport (f.normed volume) ⊆ Ioo a b := by
    rw [f.tsupport_normed_eq]
    intro s hs
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hs
    change -((b - a) / 4) ≤ s - (a + b) / 2 ∧
      s - (a + b) / 2 ≤ (b - a) / 4 at hs
    constructor <;> linarith [hs.1, hs.2]
  refine ⟨f.normed volume, f.contDiff_normed, f.hasCompactSupport_normed, hsupp, ?_⟩
  rw [intervalIntegral.integral_eq_integral_of_support_subset
    ((subset_tsupport _).trans (hsupp.trans Ioo_subset_Ioc_self))]
  exact f.integral_normed

theorem intervalL2_smooth_integral_sequence {a b : ℝ} (hab : a < b)
    (w : IntervalL2 E a b) :
    ∃ (d : ℕ → ℝ → E) (hdLp : ∀ k, MemLp (d k) 2 (volume.restrict (Icc a b))),
      (∀ k, ContDiff ℝ ∞ (d k) ∧ HasCompactSupport (d k) ∧ tsupport (d k) ⊆ Ioo a b ∧
        (∫ s in a..b, d k s) = ∫ s in a..b, w s) ∧
      Tendsto (fun k ↦ (hdLp k).toLp (d k)) atTop (𝓝 w) := by
  classical
  obtain ⟨q, hqLp, hq, hlim⟩ := intervalL2_smooth_support_sequence w
  obtain ⟨β, hβ, hβc, hβs, hβint⟩ := exists_interior_normalized_bump hab
  let μ := volume.restrict (Icc a b)
  have hβLp : MemLp β 2 μ := hβ.continuous.memLp_of_hasCompactSupport hβc
  let v : ℕ → IntervalL2 E a b := fun k ↦ (hqLp k).toLp (q k)
  let Δ : ℕ → E := fun k ↦ intervalL2_integral (w - v k)
  let d : ℕ → ℝ → E := fun k s ↦ q k s + β s • Δ k
  let L : E →L[ℝ] IntervalL2 E a b :=
    ((ContinuousLinearMap.lsmul ℝ ℝ (E := E)).flip.compLpL₂ 2 μ).flip (hβLp.toLp β)
  have hL (z : E) : (L z : ℝ → E) =ᵐ[μ] fun s ↦ β s • z := by
    change (((ContinuousLinearMap.lsmul ℝ ℝ (E := E)).flip z).compLp (hβLp.toLp β) : ℝ → E)
      =ᵐ[μ] fun s ↦ β s • z
    filter_upwards [((ContinuousLinearMap.lsmul ℝ ℝ (E := E)).flip z).coeFn_compLp
      (hβLp.toLp β), hβLp.coeFn_toLp] with s hL hs
    rw [hL, hs]
    rfl
  have hd (k : ℕ) : ContDiff ℝ ∞ (d k) :=
    (hq k).1.add (hβ.smul contDiff_const)
  have hdc (k : ℕ) : HasCompactSupport (d k) :=
    (hq k).2.1.add (hβc.smul_right (f' := fun _ ↦ Δ k))
  have hds (k : ℕ) : tsupport (d k) ⊆ Ioo a b := by
    apply (tsupport_add (q k) (fun s ↦ β s • Δ k)).trans
    exact union_subset (hq k).2.2 ((tsupport_smul_subset_left β (fun _ ↦ Δ k)).trans hβs)
  have hdLp (k : ℕ) : MemLp (d k) 2 μ :=
    (hd k).continuous.memLp_of_hasCompactSupport (hdc k)
  have hdeq (k : ℕ) : (hdLp k).toLp (d k) = v k + L (Δ k) := by
    apply Lp.ext
    filter_upwards [(hdLp k).coeFn_toLp, Lp.coeFn_add (v k) (L (Δ k)),
      (hqLp k).coeFn_toLp, hL (Δ k)] with s hd' hsum hq' hL'
    rw [hd', hsum]
    dsimp only [Pi.add_apply, v]
    rw [hq', hL']
  have hΔ (k : ℕ) : Δ k = (∫ s in a..b, w s) - (∫ s in a..b, q k s) := by
    change intervalL2_integral (w - v k) = _
    rw [map_sub, intervalL2_integral_apply hab.le, intervalL2_integral_apply hab.le]
    congr 1
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le hab.le]
    exact ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl) (hqLp k).coeFn_toLp
  refine ⟨d, hdLp, ?_, ?_⟩
  · intro k
    refine ⟨hd k, hdc k, hds k, ?_⟩
    change (∫ s in a..b, q k s + β s • Δ k) = _
    rw [intervalIntegral.integral_add (f := q k) (g := fun s ↦ β s • Δ k)
        ((hq k).1.continuous.intervalIntegrable a b)
        ((hβ.continuous.smul (continuous_const (y := Δ k))).intervalIntegrable a b),
      intervalIntegral.integral_smul_const, hβint, one_smul, hΔ]
    abel
  · have hΔlim : Tendsto Δ atTop (𝓝 (0 : E)) := by
      simpa only [Δ, v, Function.comp_def, sub_self, map_zero] using
        intervalL2_integral.continuous.tendsto (w - w) |>.comp
        (tendsto_const_nhds.sub hlim)
    have hLlim := L.continuous.tendsto 0 |>.comp hΔlim
    simpa only [hdeq, v, Function.comp_def, map_zero, add_zero] using hlim.add hLlim

theorem intervalL2_primitive_uniform {a b : ℝ}
    (v : ℕ → IntervalL2 E a b) (w : IntervalL2 E a b)
    (hlim : Tendsto v atTop (𝓝 w)) :
    TendstoUniformlyOn (fun k t ↦ ∫ s in a..t, v k s)
      (fun t ↦ ∫ s in a..t, w s) atTop (Icc a b) := by
  let μ := volume.restrict (Icc a b)
  let B : IntervalL2 ℝ a b →L[ℝ] IntervalL2 E a b →L[ℝ] E :=
    (ContinuousLinearMap.lsmul ℝ ℝ (E := E)).lpPairing μ 2 2
  let c : IntervalL2 ℝ a b := Lp.const 2 μ (1 : ℝ)
  let e (t : ℝ) : IntervalL2 ℝ a b :=
    indicatorConstLp 2 (s := Icc a t) measurableSet_Icc (measure_ne_top _ _) (1 : ℝ)
  have he (t : ℝ) : ‖e t‖ ≤ ‖c‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := μ)
      (s := Icc a t) (hs := measurableSet_Icc) (hμs := measure_ne_top _ _) (c := (1 : ℝ)),
      Lp.coeFn_const (p := (2 : ℝ≥0∞)) (μ := μ) (c := (1 : ℝ))] with s hs hc
    rw [hs, hc]
    by_cases hst : s ∈ Icc a t <;> simp [hst]
  have hBe (t : ℝ) (ht : t ∈ Icc a b) (z : IntervalL2 E a b) :
      B (e t) z = ∫ s in a..t, z s := by
    rw [show B (e t) z = ∫ s, (e t s) • z s ∂μ from
      ContinuousLinearMap.lpPairing_eq_integral
        (B := ContinuousLinearMap.lsmul ℝ ℝ (E := E)) _ _]
    calc
      _ = ∫ s, (Icc a t).indicator (fun s ↦ z s) s ∂μ := by
        apply integral_congr_ae
        filter_upwards [indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (μ := μ)
          (s := Icc a t) (hs := measurableSet_Icc) (hμs := measure_ne_top _ _) (c := (1 : ℝ))]
          with s hs
        rw [hs]
        by_cases hst : s ∈ Icc a t <;> simp [hst]
      _ = ∫ s in a..t, z s := by
        rw [integral_indicator measurableSet_Icc]
        change (∫ s in Icc a t, z s ∂volume.restrict (Icc a b)) = _
        rw [Measure.restrict_restrict_of_subset (Icc_subset_Icc_right ht.2),
          integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le ht.1]
  have herr : Tendsto (fun k ↦ (‖B‖ * ‖c‖) * ‖v k - w‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero, mul_zero] using
      (tendsto_const_nhds (x := ‖B‖ * ‖c‖)).mul
        (hlim.sub (tendsto_const_nhds (x := w))).norm
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [herr.eventually (gt_mem_nhds hε)] with k hk t ht
  rw [dist_eq_norm, ← hBe t ht, ← hBe t ht, ← map_sub]
  have hbound := (B (e t)).le_opNorm (w - v k)
  apply lt_of_le_of_lt _ hk
  calc
    ‖B (e t) (w - v k)‖ ≤ ‖B (e t)‖ * ‖w - v k‖ := hbound
    _ ≤ (‖B‖ * ‖c‖) * ‖v k - w‖ := by
      rw [norm_sub_rev]
      exact mul_le_mul_of_nonneg_right
        ((B.le_opNorm (e t)).trans (mul_le_mul_of_nonneg_left (he t) (norm_nonneg B)))
        (norm_nonneg _)

omit [CompleteSpace E] in
theorem primitive_constant_germ {d f : ℝ → E}
    (hf : ∀ s, HasDerivAt f (d s) s) {t : ℝ} (ht : t ∉ tsupport d) :
    f =ᶠ[𝓝 t] fun _ ↦ f t := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    ((isClosed_tsupport d).isOpen_compl.mem_nhds ht)
  filter_upwards [Metric.ball_mem_nhds t hε] with s hs
  apply Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball t ε).isPreconnected
    (fun r _ ↦ (hf r).differentiableAt.differentiableWithinAt) _ hs (Metric.mem_ball_self hε)
  intro r hr
  rw [(hf r).deriv]
  exact image_eq_zero_of_notMem_tsupport (hball hr)

theorem primitive_eq_left_of_support {a b : ℝ} {d f : ℝ → E}
    (hd : Continuous d) (hf : ∀ s, HasDerivAt f (d s) s)
    (hsupport : tsupport d ⊆ Ioo a b) {s : ℝ} (hs : s ≤ a) : f s = f a := by
  have hint : (∫ r in a..s, d r) = 0 := by
    calc
      _ = ∫ r in a..s, (0 : E) := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [uIcc_of_ge hs] at hr
        exact image_eq_zero_of_notMem_tsupport
          (fun h ↦ (not_lt_of_ge hr.2) (hsupport h).1)
      _ = 0 := intervalIntegral.integral_zero
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ ↦ hf r) (hd.intervalIntegrable a s)] at hint
  exact sub_eq_zero.mp hint

theorem primitive_eq_right_of_support {a b : ℝ} {d f : ℝ → E}
    (hd : Continuous d) (hf : ∀ s, HasDerivAt f (d s) s)
    (hsupport : tsupport d ⊆ Ioo a b) {s : ℝ} (hs : b ≤ s) : f s = f b := by
  have hint : (∫ r in b..s, d r) = 0 := by
    calc
      _ = ∫ r in b..s, (0 : E) := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [uIcc_of_le hs] at hr
        exact image_eq_zero_of_notMem_tsupport
          (fun h ↦ (not_lt_of_ge hr.1) (hsupport h).2)
      _ = 0 := intervalIntegral.integral_zero
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ ↦ hf r) (hd.intervalIntegrable b s)] at hint
  exact sub_eq_zero.mp hint

theorem intervalL2_smooth_primitive_sequence {a b : ℝ} (hab : a < b)
    (u : ℝ → E) (w : IntervalL2 E a b)
    (hprimitive : ∀ s ∈ Icc a b, u s = u a + ∫ r in a..s, w r) :
    ∃ (f d : ℕ → ℝ → E) (hdLp : ∀ k, MemLp (d k) 2 (volume.restrict (Icc a b))),
      (∀ k, ContDiff ℝ ∞ (f k) ∧ f k a = u a ∧ f k b = u b ∧
        (∀ s, HasDerivAt (f k) (d k s) s) ∧
        (f k =ᶠ[𝓝 a] fun _ ↦ u a) ∧ (f k =ᶠ[𝓝 b] fun _ ↦ u b) ∧
        (∀ s, s ≤ a → f k s = u a) ∧ (∀ s, b ≤ s → f k s = u b)) ∧
      TendstoUniformlyOn f u atTop (Icc a b) ∧
      Tendsto (fun k ↦ (hdLp k).toLp (d k)) atTop (𝓝 w) := by
  classical
  obtain ⟨d, hdLp, hd, hlim⟩ := intervalL2_smooth_integral_sequence hab w
  choose f hf hfa hfb hfderiv using fun k ↦
    smooth_primitive_fixed_endpoints hab (u a) (u b) (d k) (hd k).1
  have hcorr (k : ℕ) : u b - u a - ∫ r in a..b, d k r = 0 := by
    rw [(hd k).2.2.2, hprimitive b ⟨hab.le, le_rfl⟩]
    abel
  have hderiv (k : ℕ) (s : ℝ) : HasDerivAt (f k) (d k s) s := by
    simpa only [hcorr, smul_zero, add_zero] using hfderiv k s
  have hrep (k : ℕ) (t : ℝ) : f k t = u a + ∫ s in a..t, d k s := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ ↦ hderiv k s) ((hd k).1.continuous.intervalIntegrable a t), hfa]
    abel
  refine ⟨f, d, hdLp, ?_, ?_, hlim⟩
  · intro k
    refine ⟨hf k, hfa k, hfb k, hderiv k, ?_, ?_, ?_, ?_⟩
    · simpa only [hfa] using primitive_constant_germ (hderiv k)
        (fun h ↦ (lt_irrefl a) ((hd k).2.2.1 h).1)
    · simpa only [hfb] using primitive_constant_germ (hderiv k)
        (fun h ↦ (lt_irrefl b) ((hd k).2.2.1 h).2)
    · intro s hs
      exact (primitive_eq_left_of_support (hd k).1.continuous (hderiv k)
        (hd k).2.2.1 hs).trans (hfa k)
    · intro s hs
      exact (primitive_eq_right_of_support (hd k).1.continuous (hderiv k)
        (hd k).2.2.1 hs).trans (hfb k)
  · have hL := intervalL2_primitive_uniform (fun k ↦ (hdLp k).toLp (d k)) w hlim
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hL ε hε] with k hk t ht
    rw [hrep, hprimitive t ht, dist_add_left]
    have heq : (∫ s in a..t, ((hdLp k).toLp (d k)) s) = ∫ s in a..t, d k s := by
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le ht.1]
      exact ae_mono (Measure.restrict_mono
        (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right ht.2)) le_rfl) (hdLp k).coeFn_toLp
    simpa only [heq] using hk t ht

end PoincareConjecture.ReducedLengthMinimum.Variational
