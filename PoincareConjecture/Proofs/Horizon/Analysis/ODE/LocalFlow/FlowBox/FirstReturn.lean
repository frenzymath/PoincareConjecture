import PoincareConjecture.Proofs.Horizon.Analysis.ODE.LocalFlow.TransverseReturns
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact

noncomputable section

namespace Poincare.ODE.LocalFlow

open Set Filter Metric
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eq_flowBox_of_section
    {V : E → E} (hV : ContDiff ℝ ∞ V) {γ : ℝ → E}
    (hγ : ∀ t, HasDerivAt γ (V (γ t)) t)
    (e : OpenPartialHomeomorph (ℝ × ℝ) E)
    (he : ∀ s t, (s, t) ∈ e.source →
      HasDerivAt (fun u => e (s, u)) (V (e (s, t))) t)
    {ε : ℝ} (hε : 0 < ε)
    (hbox : Ioo (-ε) ε ×ˢ Ioo (-ε) ε ⊆ e.source)
    {a s : ℝ} (hs : s ∈ Ioo (-ε) ε) (ha : γ a = e (s, 0)) :
    ∀ t ∈ Ioo (-ε) ε, γ (a + t) = e (s, t) := by
  have hleft : ∀ t ∈ Ioo (-ε) ε,
      γ (a + t) ∈ (univ : Set E) ∧
        HasDerivAt (fun u => γ (a + u)) (V (γ (a + t))) t := by
    intro t _
    refine ⟨mem_univ _, ?_⟩
    simpa only [Function.comp_def, one_smul, id_eq] using
      (hγ (a + t)).scomp t ((hasDerivAt_id t).const_add a)
  apply Poincare.ODE.eqOn_of_hasDerivAt isOpen_univ hV.contDiffOn
    isOpen_Ioo (convex_Ioo (-ε) ε).isPreconnected hleft
    (fun t ht => ⟨mem_univ _, he s t (hbox ⟨hs, ht⟩)⟩)
    (show (0 : ℝ) ∈ Ioo (-ε) ε from ⟨by linarith, hε⟩)
  simpa only [add_zero] using ha

theorem flowBox_transverse_returns_of_clusterPt
    {V : E → E} (hV : ContDiff ℝ ∞ V) {γ : ℝ → E}
    (hγ : ∀ t, HasDerivAt γ (V (γ t)) t)
    (e : OpenPartialHomeomorph (ℝ × ℝ) E)
    (he : ∀ s t, (s, t) ∈ e.source →
      HasDerivAt (fun u => e (s, u)) (V (e (s, t))) t)
    {ε r : ℝ} (hr : 0 < r) (hrε : r < ε)
    (hbox : Ioo (-ε) ε ×ˢ Ioo (-ε) ε ⊆ e.source)
    (hp : MapClusterPt (e (0, 0)) atTop γ) :
    ∀ T : ℝ, ∃ t > T, ∃ s ∈ Icc (-r) r, γ t = e (s, 0) := by
  have hε : 0 < ε := hr.trans hrε
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have he0 : (0, 0) ∈ e.source := hbox ⟨hzero, hzero⟩
  let O : Set E := e.target ∩ e.symm ⁻¹' (Ioo (-r) r ×ˢ Ioo (-ε) ε)
  have hO : IsOpen O :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target (isOpen_Ioo.prod isOpen_Ioo)
  have hpO : e (0, 0) ∈ O := by
    refine ⟨e.map_source he0, ?_⟩
    change e.symm (e (0, 0)) ∈ Ioo (-r) r ×ˢ Ioo (-ε) ε
    rw [e.left_inv he0]
    exact ⟨⟨by linarith, hr⟩, hzero⟩
  intro T
  have hlate : ∃ᶠ n : ℝ in atTop, γ n ∈ O :=
    (mapClusterPt_iff_frequently.mp hp) O (hO.mem_nhds hpO)
  obtain ⟨n, hnO, hn⟩ :=
    (hlate.and_eventually (eventually_gt_atTop (T + ε))).exists
  let s : ℝ := (e.symm (γ n)).1
  let u : ℝ := (e.symm (γ n)).2
  have hs : s ∈ Ioo (-r) r := hnO.2.1
  have hsε : s ∈ Ioo (-ε) ε := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hu : u ∈ Ioo (-ε) ε := hnO.2.2
  have hvisit : γ n = e (s, u) := (e.right_inv hnO.1).symm
  let α : ℝ → E := fun t => γ (n + t - u)
  have hα : ∀ t ∈ Ioo (-ε) ε,
      α t ∈ (univ : Set E) ∧ HasDerivAt α (V (α t)) t := by
    intro t _
    refine ⟨mem_univ _, ?_⟩
    simpa only [α, Function.comp_def, one_smul, id_eq] using
      (hγ (n + t - u)).scomp t (((hasDerivAt_id t).const_add n).sub_const u)
  have hinit : α u = e (s, u) := by simpa only [α, add_sub_cancel_right] using hvisit
  have heq := Poincare.ODE.eqOn_of_hasDerivAt isOpen_univ hV.contDiffOn
    isOpen_Ioo (convex_Ioo (-ε) ε).isPreconnected hα
    (fun t ht => ⟨mem_univ _, he s t (hbox ⟨hsε, ht⟩)⟩) hu hinit
  refine ⟨n - u, by linarith [hu.2], s, ⟨hs.1.le, hs.2.le⟩, ?_⟩
  simpa only [α, add_zero] using heq hzero

private theorem exists_wider_rectangle
    {r H : ℝ} (hr : 0 < r) (hH : 0 < H) {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hsection : Icc (-r) r ×ˢ ({0} : Set ℝ) ⊆ U) :
    ∃ R h : ℝ, r < R ∧ 0 < h ∧ h < H ∧
      Icc (-R) R ×ˢ Icc (-h) h ⊆ U := by
  obtain ⟨δ, hδ, hδU⟩ :=
    (isCompact_Icc.prod isCompact_singleton).exists_cthickening_subset_open hU hsection
  let h : ℝ := min (δ / 2) (H / 2)
  have hh : 0 < h := lt_min (by positivity) (by positivity)
  have hhδ : h ≤ δ / 2 := min_le_left _ _
  have hhH : h < H := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨r + δ / 2, h, by linarith, hh, hhH, ?_⟩
  rintro ⟨s, u⟩ ⟨hs, hu⟩
  apply hδU
  have huδ : |u| ≤ δ := by
    apply abs_le.mpr
    constructor <;> linarith [hu.1, hu.2]
  by_cases hsl : s < -r
  · apply mem_cthickening_of_dist_le (s, u) (-r, 0) δ
      (Icc (-r) r ×ˢ ({0} : Set ℝ))
      ⟨⟨le_rfl, by linarith⟩, rfl⟩
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, max_le_iff]
    exact ⟨abs_le.mpr ⟨by linarith [hs.1], by linarith⟩, huδ⟩
  · by_cases hsr : r < s
    · apply mem_cthickening_of_dist_le (s, u) (r, 0) δ
        (Icc (-r) r ×ˢ ({0} : Set ℝ))
        ⟨⟨by linarith, le_rfl⟩, rfl⟩
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, max_le_iff]
      exact ⟨abs_le.mpr ⟨by linarith, by linarith [hs.2]⟩, huδ⟩
    · apply mem_cthickening_of_dist_le (s, u) (s, 0) δ
        (Icc (-r) r ×ˢ ({0} : Set ℝ))
        ⟨⟨le_of_not_gt hsl, le_of_not_gt hsr⟩, rfl⟩
      simpa only [Prod.dist_eq, dist_self, Real.dist_eq, sub_zero,
        max_le_iff, hδ.le, true_and] using huδ

theorem exists_isolated_flowBox_return
    {V : E → E} (hV : ContDiff ℝ ∞ V) {γ : ℝ → E}
    (hγ : ∀ t, HasDerivAt γ (V (γ t)) t)
    (e : OpenPartialHomeomorph (ℝ × ℝ) E)
    (he : ∀ s t, (s, t) ∈ e.source →
      HasDerivAt (fun u => e (s, u)) (V (e (s, t))) t)
    {ε r : ℝ} (hr : 0 < r) (hrε : r < ε)
    (hbox : Ioo (-ε) ε ×ˢ Ioo (-ε) ε ⊆ e.source)
    (hreturn : ∀ T : ℝ, ∃ t > T, ∃ s ∈ Icc (-r) r, γ t = e (s, 0)) :
    ∃ a b s₁ s₂ R h : ℝ,
      0 < a ∧ a + 2 * h < b ∧ r < R ∧ 0 < h ∧ h < ε / 8 ∧
      s₁ ∈ Icc (-r) r ∧ s₂ ∈ Icc (-r) r ∧
      Icc (-R) R ×ˢ Icc (-h) h ⊆ e.source ∧
      (∀ u ∈ Ioo (-ε) ε, γ (a + u) = e (s₁, u)) ∧
      (∀ u ∈ Ioo (-ε) ε, γ (b + u) = e (s₂, u)) ∧
      ∀ t ∈ Icc (a + h) (b - h),
        γ t ∉ e '' (Ioo (-R) R ×ˢ Ioo (-h) h) := by
  have hε : 0 < ε := hr.trans hrε
  have hsmall : Icc (-r) r ⊆ Ioo (-ε) ε := by
    intro s hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  let C : Set (ℝ × ℝ) := Icc (-r) r ×ˢ ({0} : Set ℝ)
  let S : Set E := e '' C
  have hC : IsCompact C := isCompact_Icc.prod isCompact_singleton
  have hCsource : C ⊆ e.source := by
    rintro ⟨s, u⟩ ⟨hs, hu⟩
    have hu0 : u = 0 := hu
    subst u
    exact hbox ⟨hsmall hs, hzero⟩
  have hS : IsCompact S := hC.image_of_continuousOn (e.continuousOn.mono hCsource)
  have hγc : Continuous γ := continuous_iff_continuousAt.mpr fun t => (hγ t).continuousAt
  obtain ⟨a, ha, s₁, hs₁, haeq⟩ := hreturn 0
  have heqa := eq_flowBox_of_section hV hγ e he hε hbox (hsmall hs₁) haeq
  have hshort (t : ℝ) (ht : t ∈ Ioo a (a + ε)) : γ t ∉ S := by
    rintro ⟨⟨s, u⟩, ⟨hs, hu⟩, hsu⟩
    have hu0 : u = 0 := hu
    subst u
    have htime : t - a ∈ Ioo (-ε) ε := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have heq : e (s₁, t - a) = e (s, 0) := by
      rw [← heqa (t - a) htime]
      simpa only [add_sub_cancel] using hsu.symm
    have hcoords := e.injOn (hbox ⟨hsmall hs₁, htime⟩) (hCsource ⟨hs, rfl⟩) heq
    have := congrArg Prod.snd hcoords
    change t - a = 0 at this
    linarith [ht.1]
  obtain ⟨c, hc, s₃, hs₃, hceq⟩ := hreturn (a + ε)
  let A : Set ℝ := Icc (a + ε / 2) c ∩ γ ⁻¹' S
  have hA : IsCompact A := isCompact_Icc.inter_right (hS.isClosed.preimage hγc)
  have hcA : c ∈ A := ⟨⟨by linarith, le_rfl⟩, ⟨(s₃, 0), ⟨hs₃, rfl⟩, hceq.symm⟩⟩
  obtain ⟨b, hb⟩ := hA.exists_isLeast ⟨c, hcA⟩
  have hbmin : a + ε / 2 ≤ b := hb.1.1.1
  have hbc : b ≤ c := hb.1.1.2
  have hab : a < b := by linarith
  obtain ⟨⟨s₂, u₂⟩, ⟨hs₂, hu₂⟩, hbpre⟩ := hb.1.2
  have hu₂0 : u₂ = 0 := hu₂
  subst u₂
  change s₂ ∈ Icc (-r) r at hs₂
  have heqb := eq_flowBox_of_section hV hγ e he hε hbox (hsmall hs₂) hbpre.symm
  have hbetween (t : ℝ) (ht : t ∈ Ioo a b) : γ t ∉ S := by
    intro htS
    by_cases htshort : t < a + ε
    · exact hshort t ⟨ht.1, htshort⟩ htS
    · have htA : t ∈ A := ⟨⟨by linarith, ht.2.le.trans hbc⟩, htS⟩
      exact (not_lt_of_ge (hb.2 htA)) ht.2
  let K : Set E := γ '' Icc (a + ε / 8) (b - ε / 8)
  have hK : IsCompact K := isCompact_Icc.image hγc
  have hKS : Disjoint K S := by
    rw [disjoint_left]
    rintro _ ⟨t, ht, rfl⟩ htS
    exact hbetween t ⟨by linarith [ht.1], by linarith [ht.2]⟩ htS
  let N : Set (ℝ × ℝ) := e.source ∩ e ⁻¹' Kᶜ
  have hN : IsOpen N :=
    e.continuousOn.isOpen_inter_preimage e.open_source hK.isClosed.isOpen_compl
  have hCN : C ⊆ N := by
    intro z hz
    refine ⟨hCsource hz, ?_⟩
    exact fun hzK => Set.disjoint_left.mp hKS hzK ⟨z, hz, rfl⟩
  obtain ⟨R, h, hrR, hh, hhε, hrect⟩ :=
    exists_wider_rectangle hr (show 0 < ε / 8 by positivity) hN hCN
  have hrectsource : Icc (-R) R ×ˢ Icc (-h) h ⊆ e.source :=
    fun z hz => (hrect hz).1
  refine ⟨a, b, s₁, s₂, R, h, ha, by linarith, hrR, hh, hhε,
    hs₁, hs₂, hrectsource, heqa, heqb, ?_⟩
  intro t ht htin
  obtain ⟨⟨s, u⟩, ⟨hs, hu⟩, hsu⟩ := htin
  have hsuclosed : (s, u) ∈ Icc (-R) R ×ˢ Icc (-h) h :=
    ⟨⟨hs.1.le, hs.2.le⟩, ⟨hu.1.le, hu.2.le⟩⟩
  have hsusource := hrectsource hsuclosed
  by_cases htleft : t < a + ε / 8
  · have htime : t - a ∈ Ioo (-ε) ε := by
      constructor <;> linarith [ht.1]
    have heq : e (s₁, t - a) = e (s, u) := by
      rw [← heqa (t - a) htime]
      simpa only [add_sub_cancel] using hsu.symm
    have hc := congrArg Prod.snd
      (e.injOn (hbox ⟨hsmall hs₁, htime⟩) hsusource heq)
    change t - a = u at hc
    linarith [ht.1, hu.2]
  · by_cases htright : b - ε / 8 < t
    · have htime : t - b ∈ Ioo (-ε) ε := by
        constructor <;> linarith [ht.2]
      have heq : e (s₂, t - b) = e (s, u) := by
        rw [← heqb (t - b) htime]
        simpa only [add_sub_cancel] using hsu.symm
      have hc := congrArg Prod.snd
        (e.injOn (hbox ⟨hsmall hs₂, htime⟩) hsusource heq)
      change t - b = u at hc
      linarith [ht.2, hu.1]
    · apply (hrect hsuclosed).2
      rw [hsu]
      exact mem_image_of_mem γ ⟨le_of_not_gt htleft, le_of_not_gt htright⟩

end Poincare.ODE.LocalFlow
