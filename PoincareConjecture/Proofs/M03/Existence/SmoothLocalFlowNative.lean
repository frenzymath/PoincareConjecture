import PoincareConjecture.Proofs.M03.Existence.ImplicitLocalFlowNative
import PoincareConjecture.Proofs.M03.Existence.CompactIntegralCurveNative
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension









set_option autoImplicit false

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff

noncomputable section

namespace PoincareConjecture.SmoothLocalFlowNative

open ImplicitLocalFlowNative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem mul_mem_timeWindow {ε t r : ℝ} (ht : t ∈ Ioo (-ε) ε)
    (hr : r ∈ Icc (0 : ℝ) 1) : t * r ∈ Ioo (-ε) ε := by
  apply abs_lt.mp
  have hmul : |t * r| ≤ |t| := by
    rw [abs_mul, abs_of_nonneg hr.1]
    exact mul_le_of_le_one_right (abs_nonneg t) hr.2
  exact hmul.trans_lt (abs_lt.mpr ht)

def rescaledPath (α : E × ℝ → E) (q : ℝ × E) : Path E :=
  ContinuousMap.mkD (fun s : UnitInterval => α (q.2, q.1 * s)) 0

theorem rescaledPath_apply {α : E × ℝ → E} {q : ℝ × E}
    (hα : Continuous (fun s : UnitInterval => α (q.2, q.1 * s)))
    (s : UnitInterval) : rescaledPath α q s = α (q.2, q.1 * s) := by
  rw [rescaledPath, ContinuousMap.mkD_of_continuous hα]
  rfl

theorem continuousOn_rescaledPath {α : E × ℝ → E} {p : E} {r ε : ℝ}
    (hα : ContinuousOn α (ball p r ×ˢ Ioo (-ε) ε)) :
    ContinuousOn (rescaledPath α) (Ioo (-ε) ε ×ˢ ball p r) := by
  apply ContinuousMap.continuousOn_mkD_of_uncurry
  apply hα.comp
    ((continuous_fst.snd.prodMk
      (continuous_fst.fst.mul continuous_snd.subtype_val)).continuousOn)
  intro q hq
  exact ⟨hq.1.2, mul_mem_timeWindow hq.1.1 q.2.property⟩

theorem continuous_rescaled_orbit {α : E × ℝ → E} {p : E} {r ε : ℝ}
    (hα : ContinuousOn α (ball p r ×ˢ Ioo (-ε) ε))
    {q : ℝ × E} (hq : q ∈ Ioo (-ε) ε ×ˢ ball p r) :
    Continuous (fun s : UnitInterval => α (q.2, q.1 * s)) := by
  apply hα.comp_continuous
    (continuous_const.prodMk (continuous_const.mul continuous_subtype_val))
  intro s
  exact ⟨hq.2, mul_mem_timeWindow hq.1 s.property⟩

def autonomousSource (F : C(E, E)) : C(ℝ × E, E) :=
  ⟨fun q => F q.2, F.continuous.comp continuous_snd⟩

theorem residual_rescaledPath (F : C(E, E)) {α : E × ℝ → E}
    {p : E} {r ε : ℝ} (hα : ContinuousOn α (ball p r ×ˢ Ioo (-ε) ε))
    (hzero : ∀ x ∈ ball p r, α (x, 0) = x)
    (hder : ∀ x ∈ ball p r, ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt (fun u => α (x, u)) (F (α (x, t))) t)
    {q : ℝ × E} (hq : q ∈ Ioo (-ε) ε ×ˢ ball p r) :
    residual (autonomousSource F) ((0, (q.1, q.2)), rescaledPath α q) = 0 := by
  let u := rescaledPath α q
  have hu := continuous_rescaled_orbit hα hq
  have hscale (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun r => α (q.2, q.1 * r))
        (q.1 • F (α (q.2, q.1 * s))) s := by
    simpa only [Function.comp_def] using
      (hder q.2 hq.2 _ (mul_mem_timeWindow hq.1 hs)).scomp s
        (hasDerivAt_const_mul q.1)
  have hcont : ContinuousOn (fun s : ℝ => α (q.2, q.1 * s)) (Icc (0 : ℝ) 1) := by
    intro s hs
    exact (hscale s hs).continuousAt.continuousWithinAt
  have hsource : ContinuousOn (fun s : ℝ => q.1 • F (α (q.2, q.1 * s)))
      (Icc (0 : ℝ) 1) := (F.continuous.comp_continuousOn hcont).const_smul q.1
  ext s
  have hinterval : Icc (0 : ℝ) s ⊆ Icc (0 : ℝ) 1 :=
    Icc_subset_Icc le_rfl s.property.2
  have hint : IntervalIntegrable (fun r => q.1 • F (α (q.2, q.1 * r)))
      volume 0 s := (hsource.mono hinterval).intervalIntegrable_of_Icc s.property.1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le s.property.1
    (hcont.mono hinterval) (fun r hr => hscale r (hinterval (mem_Icc_of_Ioo hr))) hint
  have hpoint :
      (∫ r in (0 : ℝ)..(s : ℝ),
        extendPath ((autonomousSource F).comp
          (spacetimePath ((0, (q.1, q.2)), u))) r) =
        ∫ r in (0 : ℝ)..(s : ℝ), F (α (q.2, q.1 * r)) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) 1 := by
      apply hinterval
      simpa only [uIcc_of_le s.property.1] using hr
    rw [show r = (⟨r, hr'⟩ : UnitInterval).val from rfl,
      extendPath_apply_coe, ContinuousMap.comp_apply, spacetimePath_apply]
    change F (u ⟨r, hr'⟩) = F (α (q.2, q.1 * r))
    rw [rescaledPath_apply hu]
  change u s - q.2 - q.1 •
    (∫ r in (0 : ℝ)..(s : ℝ),
      extendPath ((autonomousSource F).comp
        (spacetimePath ((0, (q.1, q.2)), u))) r) = 0
  rw [hpoint, ← intervalIntegral.integral_smul]
  rw [hFTC, mul_zero, hzero q.2 hq.2, rescaledPath_apply hu]
  exact sub_self _

theorem contDiffOn_flow_near_initial_of_order {k : ℕ∞}
    (F : C(E, E)) (hF : ContDiff ℝ k (F : E → E)) (hk : k ≠ 0)
    {α : E × ℝ → E} {p : E} {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hα : ContinuousOn α (ball p r ×ˢ Ioo (-ε) ε))
    (hzero : ∀ x ∈ ball p r, α (x, 0) = x)
    (hder : ∀ x ∈ ball p r, ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt (fun u => α (x, u)) (F (α (x, t))) t) :
    ∃ S : Set (E × ℝ), IsOpen S ∧ (p, 0) ∈ S ∧ ContDiffOn ℝ k α S := by
  obtain ⟨U, S, hSo, hpS, hU, _, _, hUnique⟩ :=
    exists_contDiff_integral_path_on (autonomousSource F) (hF.comp contDiff_snd) hk 0 p
  let embed : ℝ × E → Parameters E := fun q => (0, (q.1, q.2))
  have hembed : ContDiff ℝ k embed := contDiff_const.prodMk
    (contDiff_fst.prodMk contDiff_snd)
  have hbox : Ioo (-ε) ε ×ˢ ball p r ∈ 𝓝 ((0 : ℝ), p) :=
    prod_mem_nhds (Ioo_mem_nhds (neg_lt_zero.mpr hε) hε) (ball_mem_nhds p hr)
  have hbase : rescaledPath α (0, p) = ContinuousMap.const UnitInterval p := by
    ext s
    rw [rescaledPath_apply (continuous_rescaled_orbit hα
      ⟨⟨neg_lt_zero.mpr hε, hε⟩, mem_ball_self hr⟩), zero_mul, hzero p (mem_ball_self hr)]
    rfl
  have hpaths : ContinuousAt (rescaledPath α) (0, p) :=
    (continuousOn_rescaledPath hα).continuousAt hbox
  have hgraph : Tendsto (fun q => (embed q, rescaledPath α q))
      (𝓝 ((0 : ℝ), p))
      (𝓝 ((0, (0, p)), ContinuousMap.const UnitInterval p)) := by
    simpa only [embed, hbase, nhds_prod_eq] using
      hembed.continuous.continuousAt.tendsto.prodMk hpaths
  have hequal : ∀ᶠ q : ℝ × E in 𝓝 (0, p),
      α (q.2, q.1) = U (embed q) unitOne := by
    filter_upwards [hgraph.eventually hUnique, hbox] with q hq hqb
    have hq' := hq (residual_rescaledPath F hα hzero hder hqb)
    have hvalue := congrArg (fun u : Path E => u unitOne) hq'
    simpa only [rescaledPath_apply (continuous_rescaled_orbit hα hqb),
      unitOne, mul_one] using hvalue.symm
  have hS : embed ⁻¹' S ∈ 𝓝 ((0 : ℝ), p) :=
    hembed.continuous.continuousAt.preimage_mem_nhds (hSo.mem_nhds hpS)
  obtain ⟨A, hA, hAo, hpA⟩ := _root_.mem_nhds_iff.mp (Filter.inter_mem hequal hS)
  have hEndpoint : ContDiffOn ℝ k (fun q => U (embed q) unitOne) A :=
    (ContinuousMap.evalCLM ℝ unitOne : Path E →L[ℝ] E).contDiff.comp_contDiffOn
      (hU.comp hembed.contDiffOn (fun q hq => (hA hq).2))
  have hswap : ContDiffOn ℝ k (fun q : ℝ × E => α (q.2, q.1)) A :=
    hEndpoint.congr (fun q hq => (hA hq).1)
  refine ⟨Prod.swap ⁻¹' A, hAo.preimage continuous_swap, hpA, ?_⟩
  exact hswap.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun q hq => hq)

theorem contDiffOn_flow_near_initial (F : C(E, E)) (hF : ContDiff ℝ ∞ (F : E → E))
    {α : E × ℝ → E} {p : E} {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hα : ContinuousOn α (ball p r ×ˢ Ioo (-ε) ε))
    (hzero : ∀ x ∈ ball p r, α (x, 0) = x)
    (hder : ∀ x ∈ ball p r, ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt (fun u => α (x, u)) (F (α (x, t))) t) :
    ∃ S : Set (E × ℝ), IsOpen S ∧ (p, 0) ∈ S ∧ ContDiffOn ℝ ∞ α S :=
  contDiffOn_flow_near_initial_of_order F hF (by simp) hr hε hα hzero hder

theorem exists_contDiff_confined_local_flow {k : ℕ∞} (hk : k ≠ 0)
    (F : E → E) (hF : ContDiff ℝ k F)
    (p : E) {s : Set E} (hs : s ∈ 𝓝 p) :
    ∃ r > 0, ∃ ε > 0, ∃ α : E × ℝ → E,
      (∀ x ∈ ball p r, α (x, 0) = x) ∧
      (∀ x ∈ ball p r, ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (fun u => α (x, u)) (F (α (x, t))) t ∧ α (x, t) ∈ s) ∧
      ContDiffOn ℝ k α (ball p r ×ˢ Ioo (-ε) ε) := by
  obtain ⟨r, hr, ε, hε, α, hzero, hder, hcont⟩ :=
    CompactIntegralCurveNative.exists_confined_local_flow
      ((hF.of_le (by exact_mod_cast (Order.one_le_iff_ne_zero.mpr hk : (1 : ℕ∞) ≤ k))).contDiffAt) hs
  obtain ⟨A, hAo, hpA, hA⟩ :=
    contDiffOn_flow_near_initial_of_order ⟨F, hF.continuous⟩ hF hk hr hε hcont hzero
      (fun x hx t ht => (hder x hx t ht).1)
  obtain ⟨δ, hδ, hδA⟩ := Metric.mem_nhds_iff.mp (hAo.mem_nhds hpA)
  let r' := min r δ
  let ε' := min ε δ
  have hr' : 0 < r' := lt_min hr hδ
  have hε' : 0 < ε' := lt_min hε hδ
  have hxold {x : E} (hx : x ∈ ball p r') : x ∈ ball p r :=
    ball_subset_ball (min_le_left _ _) hx
  have htold {t : ℝ} (ht : t ∈ Ioo (-ε') ε') : t ∈ Ioo (-ε) ε :=
    Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _) ht
  refine ⟨r', hr', ε', hε', α, (fun x hx => hzero x (hxold hx)),
    (fun x hx t ht => hder x (hxold hx) t (htold ht)), hA.mono ?_⟩
  intro q hq
  apply hδA
  rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
  refine ⟨(mem_ball.mp hq.1).trans_le (min_le_right _ _), ?_⟩
  rw [Real.dist_eq, sub_zero]
  exact (abs_lt.mpr hq.2).trans_le (min_le_right _ _)

theorem exists_smooth_confined_local_flow (F : E → E) (hF : ContDiff ℝ ∞ F)
    (p : E) {s : Set E} (hs : s ∈ 𝓝 p) :
    ∃ r > 0, ∃ ε > 0, ∃ α : E × ℝ → E,
      (∀ x ∈ ball p r, α (x, 0) = x) ∧
      (∀ x ∈ ball p r, ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (fun u => α (x, u)) (F (α (x, t))) t ∧ α (x, t) ∈ s) ∧
      ContDiffOn ℝ ∞ α (ball p r ×ˢ Ioo (-ε) ε) :=
  exists_contDiff_confined_local_flow (by simp) F hF p hs

theorem exists_contDiff_confined_local_flow_on [FiniteDimensional ℝ E]
    {k : ℕ∞} (hk : k ≠ 0)
    (F : E → E) {V : Set E} (hV : IsOpen V) (hF : ContDiffOn ℝ k F V)
    (p : E) (hp : p ∈ V) {s : Set E} (hs : s ∈ 𝓝 p) :
    ∃ r > 0, ∃ ε > 0, ∃ α : E × ℝ → E,
      (∀ x ∈ ball p r, α (x, 0) = x) ∧
      (∀ x ∈ ball p r, ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (fun u => α (x, u)) (F (α (x, t))) t ∧ α (x, t) ∈ s) ∧
      ContDiffOn ℝ k α (ball p r ×ˢ Ioo (-ε) ε) := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hp)
  let β : ContDiffBump p :=
    { rIn := δ / 4
      rOut := δ / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hβV : tsupport β ⊆ V := by
    rw [β.tsupport_eq]
    intro y hy
    apply hsub
    exact lt_of_le_of_lt (mem_closedBall.mp hy) (by dsimp [β]; linarith)
  let G : E → E := fun y => β y • F y
  have hG : ContDiff ℝ k G := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ tsupport β
    · exact β.contDiffAt.smul (hF.contDiffAt (hV.mem_nhds (hβV hy)))
    · apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
      simp only [G, hz, Pi.zero_apply, zero_smul]
  obtain ⟨r, hr, ε, hε, α, hzero, hder, hα⟩ :=
    exists_contDiff_confined_local_flow hk G hG p
      (Filter.inter_mem hs (ball_mem_nhds p β.rIn_pos))
  refine ⟨r, hr, ε, hε, α, hzero, ?_, hα⟩
  intro x hx t ht
  obtain ⟨hd, hs, hb⟩ := hder x hx t ht
  refine ⟨?_, hs⟩
  have hvalue : G (α (x, t)) = F (α (x, t)) := by
    change β (α (x, t)) • F (α (x, t)) = F (α (x, t))
    rw [β.one_of_mem_closedBall (ball_subset_closedBall hb), one_smul]
  exact hd.congr_deriv hvalue

theorem exists_smooth_confined_local_flow_on [FiniteDimensional ℝ E]
    (F : E → E) {V : Set E} (hV : IsOpen V) (hF : ContDiffOn ℝ ∞ F V)
    (p : E) (hp : p ∈ V) {s : Set E} (hs : s ∈ 𝓝 p) :
    ∃ r > 0, ∃ ε > 0, ∃ α : E × ℝ → E,
      (∀ x ∈ ball p r, α (x, 0) = x) ∧
      (∀ x ∈ ball p r, ∀ t ∈ Ioo (-ε) ε,
        HasDerivAt (fun u => α (x, u)) (F (α (x, t))) t ∧ α (x, t) ∈ s) ∧
      ContDiffOn ℝ ∞ α (ball p r ×ˢ Ioo (-ε) ε) :=
  exists_contDiff_confined_local_flow_on (by simp) F hV hF p hp hs

end PoincareConjecture.SmoothLocalFlowNative

end
