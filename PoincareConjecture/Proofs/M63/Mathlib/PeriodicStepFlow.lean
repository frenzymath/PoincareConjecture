import PoincareConjecture.Proofs.M63.Mathlib.CompactScalarStepFlow
import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.Normed.Group.Bounded











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Manifold
open scoped Topology ContDiff Bundle




theorem exists_periodic_step_flow {L : ℝ} (hL : 0 < L)
    {k : ℕ} (hk : 1 ≤ k) (Y : ℝ → ℝ → ℝ)
    (hY : ContDiff ℝ k (Function.uncurry Y))
    (hper : ∀ t, Function.Periodic (Y t) L) :
    ∃ ε > 0, ∃ A : ℝ → ℝ → ℝ → ℝ,
      (∀ s ∈ Ioo (-1 : ℝ) 1, ∀ x, A s x 0 = x) ∧
      (∀ s ∈ Ioo (-1 : ℝ) 1, ∀ x, ∀ u ∈ Ioo (-ε) ε,
        HasDerivAt (fun r => A s x r) (Y (s + u) (A s x u)) u) ∧
      (∀ s ∈ Ioo (-1 : ℝ) 1, ∀ x, ∀ u ∈ Ioo (-ε) ε,
        A s (x + L) u = A s x u + L) ∧
      ContDiffOn ℝ k (fun z : ℝ × ℝ × ℝ => A z.1 z.2.1 z.2.2)
        (Ioo (-1 : ℝ) 1 ×ˢ (univ ×ˢ Ioo (-ε) ε)) ∧
      (∀ s ∈ Ioo (-1 : ℝ) 1, ∀ u ∈ Ioo (-ε) ε, ∀ x,
        0 < deriv (fun y => A s y u) x) ∧
      ∀ s ∈ Ioo (-1 : ℝ) 1, ∀ u ∈ Ioo (-ε) ε,
        Function.Bijective (fun x => A s x u) := by
  classical
  have hk0 : (k : ℕ∞) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hk0' : (k : ℕ∞ω) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hk1 : (1 : ℕ∞ω) ≤ k := by exact_mod_cast hk
  let K : Set (ℝ × ℝ) := Icc (-1) 1 ×ˢ Icc (-L) (2 * L)
  obtain ⟨U, hU, hKU, ε, hε, f, hf0, hft, hf⟩ :=
    exists_contDiff_scalar_local_flow_on_compact hk0 Y hY
      (show IsCompact K from isCompact_Icc.prod isCompact_Icc)
  have hdom : IsOpen (U ×ˢ Ioo (-ε) ε) := hU.prod isOpen_Ioo
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
  let r : ℝ → ℝ := toIcoMod hL 0
  let j : ℝ → ℤ := toIcoDiv hL 0
  have hr (x : ℝ) : r x ∈ Ico 0 L := toIcoMod_mem_Ico' hL x
  have hsplit (x : ℝ) : r x + j x • L = x :=
    toIcoMod_add_toIcoDiv_zsmul hL 0 x
  have hsub (x : ℝ) : x - j x • L = r x := by linarith [hsplit x]
  have hinit (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 1) (x : ℝ) : (s, r x) ∈ U :=
    hKU ⟨⟨hs.1.le, hs.2.le⟩, ⟨by linarith [(hr x).1], by linarith [(hr x).2]⟩⟩
  let A : ℝ → ℝ → ℝ → ℝ := fun s x u => f ((s, r x), u) + j x • L
  have hA0 (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 1) (x : ℝ) : A s x 0 = x := by
    dsimp only [A]
    rw [hf0 _ (hinit s hs x)]
    exact hsplit x
  have htranslated (s y : ℝ) (hp : (s, y) ∈ U) (n : ℤ)
      (u : ℝ) (hu : u ∈ Ioo (-ε) ε) :
      HasDerivAt (fun v => f ((s, y), v) + n • L)
        (Y (s + u) (f ((s, y), u) + n • L)) u := by
    rw [(hper (s + u)).zsmul n]
    exact (hft (s, y) hp u hu).add_const (n • L)
  have hAt (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 1) (x u : ℝ)
      (hu : u ∈ Ioo (-ε) ε) :
      HasDerivAt (fun v => A s x v) (Y (s + u) (A s x u)) u :=
    htranslated s (r x) (hinit s hs x) (j x) u hu
  let V : (p : ℝ × ℝ) → TangentSpace 𝓘(ℝ, ℝ × ℝ) p :=
    fun p => (1, Y p.1 p.2)
  have hV : ContMDiff 𝓘(ℝ, ℝ × ℝ)
      (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, ℝ × ℝ)) 1
      (fun p => (⟨p, V p⟩ : TangentBundle 𝓘(ℝ, ℝ × ℝ) (ℝ × ℝ))) :=
    contMDiff_vectorSpace_iff_contDiff.mpr (contDiff_const.prodMk (hY.of_le hk1))
  have hfixed (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 1) (x : ℝ) (n : ℤ)
      (hx : x - n • L ∈ Icc (-L) (2 * L)) (u : ℝ) (hu : u ∈ Ioo (-ε) ε) :
      A s x u = f ((s, x - n • L), u) + n • L := by
    have hp : (s, x - n • L) ∈ U := hKU ⟨⟨hs.1.le, hs.2.le⟩, hx⟩
    have hca : IsMIntegralCurveOn (fun v => (s + v, A s x v)) V (Ioo (-ε) ε) := by
      intro v hv
      have hd := ((hasDerivAt_id v).const_add s).prodMk (hAt s hs x v hv)
      exact hd.hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
    have hcb : IsMIntegralCurveOn
        (fun v => (s + v, f ((s, x - n • L), v) + n • L)) V (Ioo (-ε) ε) := by
      intro v hv
      exact (((hasDerivAt_id v).const_add s).prodMk
        (htranslated s (x - n • L) hp n v hv)).hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt
    have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless hzero hV hca hcb
      (by simp only [hA0 s hs x, hf0 _ hp, add_zero, sub_add_cancel])
    exact congrArg Prod.snd (heq hu)
  have hAreg : ContDiffOn ℝ k (fun z : ℝ × ℝ × ℝ => A z.1 z.2.1 z.2.2)
      (Ioo (-1 : ℝ) 1 ×ˢ (univ ×ˢ Ioo (-ε) ε)) := by
    intro z hz
    let n := j z.2.1
    have hrep : z.2.1 - n • L ∈ Ioo (-L) (2 * L) := by
      rw [show n = j z.2.1 from rfl, hsub]
      exact ⟨by linarith [(hr z.2.1).1], by linarith [(hr z.2.1).2]⟩
    have hp : (z.1, z.2.1 - n • L) ∈ U :=
      hKU ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hrep.1.le, hrep.2.le⟩⟩
    have hG : ContDiffAt ℝ k
        (fun w : ℝ × ℝ × ℝ => f ((w.1, w.2.1 - n • L), w.2.2) + n • L) z :=
      ((hf.contDiffAt (hdom.mem_nhds ⟨hp, hz.2.2⟩)).comp z
        ((contDiffAt_fst.prodMk (contDiffAt_snd.fst.sub contDiffAt_const)).prodMk
          contDiffAt_snd.snd)).add contDiffAt_const
    have hnear : ∀ᶠ w : ℝ × ℝ × ℝ in 𝓝 z,
        w.2.1 - n • L ∈ Ioo (-L) (2 * L) :=
      ((continuous_snd.fst.sub continuous_const).continuousAt)
        (Ioo_mem_nhds hrep.1 hrep.2)
    have hdomain : Ioo (-1 : ℝ) 1 ×ˢ (univ ×ˢ Ioo (-ε) ε) ∈ 𝓝 z :=
      (isOpen_Ioo.prod (isOpen_univ.prod isOpen_Ioo)).mem_nhds hz
    have heq : (fun w : ℝ × ℝ × ℝ => A w.1 w.2.1 w.2.2) =ᶠ[𝓝 z]
        (fun w => f ((w.1, w.2.1 - n • L), w.2.2) + n • L) := by
      filter_upwards [hnear, hdomain] with w hw hd
      exact hfixed w.1 hd.1 w.2.1 n ⟨hw.1.le, hw.2.le⟩ w.2.2 hd.2.2
    exact (hG.congr_of_eventuallyEq heq).contDiffWithinAt
  let D : (ℝ × ℝ) × ℝ → ℝ := fun z => fderiv ℝ f z ((0, 1), 0)
  have hDc : ContinuousOn D (U ×ˢ Ioo (-ε) ε) :=
    (hf.continuousOn_fderiv_of_isOpen hdom hk1).clm_apply continuousOn_const
  have hD0 (p : ℝ × ℝ) (hp : p ∈ U) : D (p, 0) = 1 := by
    have hdiff : DifferentiableAt ℝ f (p, 0) :=
      (hf.contDiffAt (hdom.mem_nhds ⟨hp, hzero⟩)).differentiableAt hk0'
    have hd := hdiff.hasFDerivAt.comp_hasDerivAt p.2
        (((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)).prodMk
          (hasDerivAt_const p.2 (0 : ℝ)))
    change HasDerivAt (fun y => f ((p.1, y), 0)) (D (p, 0)) p.2 at hd
    have hnear : ∀ᶠ y : ℝ in 𝓝 p.2, (p.1, y) ∈ U :=
      (continuousAt_const.prodMk continuousAt_id) (hU.mem_nhds hp)
    have heq : (fun y => f ((p.1, y), 0)) =ᶠ[𝓝 p.2] (fun y => y) := by
      filter_upwards [hnear] with y hy
      exact hf0 _ hy
    exact hd.unique ((hasDerivAt_id p.2).congr_of_eventuallyEq heq)
  let K0 : Set (ℝ × ℝ) := Icc (-1) 1 ×ˢ Icc 0 L
  have hK0 : IsCompact K0 := isCompact_Icc.prod isCompact_Icc
  have hK0U : K0 ⊆ U := by
    intro p hp
    exact hKU ⟨hp.1, ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩⟩
  have hpositive : ∀ᶠ u : ℝ in 𝓝 0, ∀ p ∈ K0, (1 / 2 : ℝ) < D (p, u) := by
    apply hK0.eventually_forall_of_forall_eventually
    intro p hp
    have hd : ContinuousAt D (p, 0) :=
      (hDc (p, 0) ⟨hK0U hp, hzero⟩).continuousAt (hdom.mem_nhds ⟨hK0U hp, hzero⟩)
    have hc : ContinuousAt (fun z : ℝ × (ℝ × ℝ) => D (z.2, z.1)) (0, p) :=
      ContinuousAt.comp (g := D) (f := fun z : ℝ × (ℝ × ℝ) => (z.2, z.1))
        hd (continuousAt_snd.prodMk continuousAt_fst)
    exact hc (Ioi_mem_nhds (show (1 / 2 : ℝ) < D (p, 0) by rw [hD0 p (hK0U hp)]; norm_num))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpositive
  let η := min ε δ
  have hη : 0 < η := lt_min hε hδ
  have hwindow : Ioo (-η) η ⊆ Ioo (-ε) ε :=
    Ioo_subset_Ioo (neg_le_neg (min_le_left ε δ)) (min_le_left ε δ)
  have hDpos (p : ℝ × ℝ) (hp : p ∈ K0) (u : ℝ) (hu : u ∈ Ioo (-η) η) :
      0 < D (p, u) := by
    have huδ : u ∈ Metric.ball (0 : ℝ) δ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
      exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_right ε δ)) hu.1,
        lt_of_lt_of_le hu.2 (min_le_right ε δ)⟩
    have h := hball huδ p hp
    linarith
  have hAx (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 1) (u : ℝ)
      (hu : u ∈ Ioo (-ε) ε) (x : ℝ) :
      HasDerivAt (fun y => A s y u) (D ((s, r x), u)) x := by
    have hp := hinit s hs x
    have hdiff : DifferentiableAt ℝ f ((s, r x), u) :=
      (hf.contDiffAt (hdom.mem_nhds ⟨hp, hu⟩)).differentiableAt hk0'
    have hd := hdiff.hasFDerivAt.comp_hasDerivAt x
        (((hasDerivAt_const x s).prodMk ((hasDerivAt_id x).sub_const (j x • L))).prodMk
          (hasDerivAt_const x u))
    have hdf : HasDerivAt (fun y => f ((s, y - j x • L), u) + j x • L)
        (D ((s, r x), u)) x := hd.add_const (j x • L)
    have hrep : x - j x • L ∈ Ioo (-L) (2 * L) := by
      rw [hsub]
      exact ⟨by linarith [(hr x).1], by linarith [(hr x).2]⟩
    have hnear : ∀ᶠ y : ℝ in 𝓝 x, y - j x • L ∈ Ioo (-L) (2 * L) :=
      (continuousAt_id.sub continuousAt_const) (Ioo_mem_nhds hrep.1 hrep.2)
    apply hdf.congr_of_eventuallyEq
    filter_upwards [hnear] with y hy
    exact hfixed s hs y (j x) ⟨hy.1.le, hy.2.le⟩ u hu
  have hderivpos (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 1) (u : ℝ)
      (hu : u ∈ Ioo (-η) η) (x : ℝ) : 0 < deriv (fun y => A s y u) x := by
    rw [(hAx s hs u (hwindow hu) x).deriv]
    exact hDpos (s, r x) ⟨⟨hs.1.le, hs.2.le⟩, (hr x).1, (hr x).2.le⟩ u hu
  refine ⟨η, hη, A, hA0, fun s hs x u hu => hAt s hs x u (hwindow hu), ?_,
    hAreg.mono (prod_mono Subset.rfl (prod_mono Subset.rfl hwindow)), hderivpos, ?_⟩
  · intro s _hs x u _hu
    dsimp only [A, r, j]
    rw [toIcoMod_add_right, toIcoDiv_add_right, add_zsmul, one_zsmul]
    abel
  · intro s hs u hu
    have hd (x : ℝ) := hAx s hs u (hwindow hu) x
    have hmono : StrictMono (fun x => A s x u) :=
      strictMono_of_hasDerivAt_pos hd (fun x => by rw [← (hd x).deriv]; exact hderivpos s hs u hu x)
    refine ⟨hmono.injective, ?_⟩
    have hdisp : ContinuousOn (fun y => f ((s, y), u) - y) (Icc 0 L) := by
      apply ContinuousOn.sub ?_ continuousOn_id
      apply hf.continuousOn.comp
        (continuous_const.prodMk continuous_id |>.prodMk continuous_const).continuousOn
      intro y hy
      exact ⟨hK0U ⟨⟨hs.1.le, hs.2.le⟩, hy⟩, hwindow hu⟩
    obtain ⟨C0, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hdisp
    let C := max C0 0
    have hCnonneg : 0 ≤ C := le_max_right _ _
    have hbound (x : ℝ) : |A s x u - x| ≤ C := by
      have h := (hC (r x) ⟨(hr x).1, (hr x).2.le⟩).trans (le_max_left C0 0)
      have heq : A s x u - x = f ((s, r x), u) - r x := by
        dsimp only [A]
        linarith [hsplit x]
      simpa only [heq, Real.norm_eq_abs] using h
    intro z
    have hl := (abs_le.mp (hbound (z - C - 1))).2
    have hr' := (abs_le.mp (hbound (z + C + 1))).1
    have hc : Continuous (fun x => A s x u) := continuous_iff_continuousAt.mpr
      (fun x => (hd x).continuousAt)
    obtain ⟨x, _hx, heq⟩ := intermediate_value_Icc
      (show z - C - 1 ≤ z + C + 1 by linarith) hc.continuousOn
      (show z ∈ Icc (A s (z - C - 1) u) (A s (z + C + 1) u) from
        ⟨by linarith, by linarith⟩)
    exact ⟨x, heq⟩
