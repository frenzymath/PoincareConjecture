import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegularLoop
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.Coordinates

noncomputable section
set_option autoImplicit false

open Set Filter Metric
open scoped Topology ContDiff

namespace PoincareConjecture

theorem m64Intrinsic_loop_graph_neighborhood
    {gamma : ℝ → AnnulusCoordinates} (hg : Continuous gamma) {T : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (G : OpenPartialHomeomorph ℝ ℝ) (h : ℝ → ℝ)
    {a b l r : ℝ} (hab : a ≤ b) (ha : 0 < a) (hb : b < T)
    (hla : l < a) (hbr : b < r) (hsource : G.source = Ioo l r)
    (hmono : StrictMonoOn G G.source)
    (hgraph : ∀ t ∈ G.source, L (gamma t) = (G t, h (G t))) :
    ∃ W : Set AnnulusCoordinates, IsOpen W ∧ gamma '' Icc a b ⊆ W ∧
      ∀ z ∈ W, (L z).1 ∈ G.target ∧
        (z ∈ gamma '' Icc 0 T ↔ (L z).2 = h (L z).1) := by
  let c := (max l 0 + a) / 2
  let d := (b + min r T) / 2
  have hc : max l 0 < c ∧ c < a := by
    have hlt := max_lt hla ha
    dsimp only [c]
    constructor <;> linarith
  have hd : b < d ∧ d < min r T := by
    have hlt := lt_min hbr hb
    dsimp only [d]
    constructor <;> linarith
  have hcd : c < d := hc.2.trans_le hab |>.trans hd.1
  have hc0 : 0 < c := (le_max_right l 0).trans_lt hc.1
  have hdT : d < T := hd.2.trans_le (min_le_right r T)
  have hJ : Icc c d ⊆ G.source := by
    rw [hsource]
    exact fun _ ht => ⟨(le_max_left l 0).trans_lt (hc.1.trans_le ht.1),
      ht.2.trans_lt (hd.2.trans_le (min_le_left r T))⟩
  have hI : Icc a b ⊆ Ioo c d :=
    fun _ ht => ⟨hc.2.trans_le ht.1, ht.2.trans_lt hd.1⟩
  let tail : Set AnnulusCoordinates := gamma '' (Icc 0 c ∪ Icc d T)
  have htail : IsClosed tail :=
    ((isCompact_Icc.union isCompact_Icc).image hg).isClosed
  let W : Set AnnulusCoordinates := {z | (L z).1 ∈ Ioo (G c) (G d)} \ tail
  have hW : IsOpen W := (isOpen_Ioo.preimage L.continuous.fst).sdiff htail
  have havoid (x : ℝ) (hx : x ∈ Icc a b) : gamma x ∉ tail := by
    rintro ⟨y, hy, hyx⟩
    have hxI : x ∈ Ico 0 T := ⟨ha.le.trans hx.1, hx.2.trans_lt hb⟩
    have hyI : y ∈ Icc 0 T := by
      rcases hy with hy | hy
      · exact ⟨hy.1, hy.2.trans (hcd.le.trans hdT.le)⟩
      · exact ⟨(hc0.le.trans hcd.le).trans hy.1, hy.2⟩
    have hylt : y < T := by
      by_contra hn
      have hyT : y = T := le_antisymm hyI.2 (le_of_not_gt hn)
      have h0x : gamma 0 = gamma x := hend.trans (hyT ▸ hyx)
      have hx0 := hinj ⟨le_rfl, ha.trans_le hab |>.trans hb⟩ hxI h0x
      linarith [ha.trans_le hx.1]
    have hyx' := hinj ⟨hyI.1, hylt⟩ hxI hyx
    subst y
    rcases hy with hy | hy
    · exact not_le_of_gt (hI hx).1 hy.2
    · exact not_le_of_gt (hI hx).2 hy.1
  have himage : G '' Icc c d = Icc (G c) (G d) :=
    (G.continuousOn.mono hJ).image_Icc_of_monotoneOn hcd.le (hmono.monotoneOn.mono hJ)
  refine ⟨W, hW, ?_, ?_⟩
  · rintro z ⟨t, ht, rfl⟩
    have htG := hJ (Ioo_subset_Icc_self (hI ht))
    refine ⟨?_, havoid t ht⟩
    change (L (gamma t)).1 ∈ Ioo (G c) (G d)
    rw [hgraph t htG]
    exact ⟨hmono (hJ (left_mem_Icc.mpr hcd.le)) htG (hI ht).1,
      hmono htG (hJ (right_mem_Icc.mpr hcd.le)) (hI ht).2⟩
  · intro z hz
    have hximage : (L z).1 ∈ G '' Icc c d := by
      rw [himage]
      exact Ioo_subset_Icc_self hz.1
    have hxtarget : (L z).1 ∈ G.target := by
      obtain ⟨t, ht, heq⟩ := hximage
      rw [← heq]
      exact G.map_source (hJ ht)
    refine ⟨hxtarget, ?_⟩
    constructor
    · rintro ⟨t, ht, rfl⟩
      have htcd : t ∈ Ioo c d := by
        constructor
        · by_contra hn
          exact hz.2 ⟨t, Or.inl ⟨ht.1, le_of_not_gt hn⟩, rfl⟩
        · by_contra hn
          exact hz.2 ⟨t, Or.inr ⟨le_of_not_gt hn, ht.2⟩, rfl⟩
      rw [hgraph t (hJ (Ioo_subset_Icc_self htcd))]
    · intro hzgraph
      obtain ⟨t, ht, heq⟩ := hximage
      refine ⟨t, ⟨hc0.le.trans ht.1, ht.2.trans hdT.le⟩, ?_⟩
      apply L.injective
      rw [hgraph t (hJ ht), heq]
      exact Prod.ext rfl hzgraph.symm

theorem m64Intrinsic_exists_regular_loop_graph_neighborhood
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T p : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hp : p ∈ Ioo (0 : ℝ) T) (hregular : deriv gamma p ≠ 0) :
    ∃ (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ)) (h : ℝ → ℝ)
      (X : Set ℝ) (W : Set AnnulusCoordinates),
      IsOpen X ∧ ContDiffOn ℝ ∞ h X ∧ IsOpen W ∧ gamma p ∈ W ∧
      ∀ z ∈ W, (L z).1 ∈ X ∧ (z ∈ gamma '' Icc 0 T ↔ (L z).2 = h (L z).1) := by
  let v := deriv gamma p
  have hderiv : Continuous (deriv gamma) := (contDiff_infty_iff_deriv.mp hg).2.continuous
  have hpos : {t | 0 < inner ℝ v (deriv gamma t)} ∈ 𝓝 p :=
    (isOpen_lt continuous_const (continuous_const.inner hderiv)).mem_nhds
      (real_inner_self_pos.mpr hregular)
  obtain ⟨l, r, ⟨hlp, hpr⟩, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (inter_mem (isOpen_Ioo.mem_nhds hp) hpos)
  let a := (l + p) / 2
  let b := (p + r) / 2
  have hap : a < p := by dsimp only [a]; linarith
  have hpb : p < b := by dsimp only [b]; linarith
  have hla : l < a := by dsimp only [a]; linarith
  have hbr : b < r := by dsimp only [b]; linarith
  have hab : a < b := hap.trans hpb
  have hI : Icc a b ⊆ Ioo l r :=
    fun _ ht => ⟨hla.trans_le ht.1, ht.2.trans_lt hbr⟩
  obtain ⟨l', r', G, L, h, hl'a, hbr', hsource, hG, _, hmono,
    _, _, _, hh, hgraph, _, _, _⟩ :=
    Poincare.Topology.Plane.Curves.exists_graph_coordinates_of_positive_projection hg hab.le
      (fun t ht => (hsub (hI ht)).2)
  have hmonoG : StrictMonoOn G G.source := by
    intro x hx y hy hxy
    simpa only [hG] using hmono hx hy hxy
  obtain ⟨W, hW, harc, hWgraph⟩ := m64Intrinsic_loop_graph_neighborhood hg.continuous
    hend hinj L G h hab.le (hsub (hI (left_mem_Icc.mpr hab.le))).1.1
      (hsub (hI (right_mem_Icc.mpr hab.le))).1.2 hl'a hbr' hsource hmonoG hgraph
  exact ⟨L, h, G.target, W, G.open_target, hh, hW,
    harc ⟨p, ⟨hap.le, hpb.le⟩, rfl⟩, hWgraph⟩

end PoincareConjecture
