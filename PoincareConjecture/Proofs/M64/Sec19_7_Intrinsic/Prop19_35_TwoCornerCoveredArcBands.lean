import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoCornerArcBands
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcShortBandJoinCoverage
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcRetainedCapCoverage
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcTrimmedBandCoverage

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture

theorem m64Intrinsic_exists_two_corner_covered_arc_bands
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ}
    (hinj : InjOn gamma (Icc 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    {K U V : Set AnnulusCoordinates} (hK : IsCompact K)
    (havoid : ∀ t ∈ Ioo (0 : ℝ) T, gamma t ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = gamma '' Icc 0 T ∪ K) (hfV : frontier V = frontier U)
    (hray : ∀ t ∈ Ioo (0 : ℝ) T, ∀ᶠ z in 𝓝[>] (0 : ℝ),
      gamma t + z • quarterTurn (deriv gamma t) ∈ U)
    (r : Bool → ℝ) (hr : ∀ e, 0 < r e) (hrbound : ∀ e, r e ≤ T / 3)
    (H : Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (F : Bool → Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (positive vertical : Bool → Bool)
    (hsource : ∀ e i,
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e} ⊆ (F e i).source)
    (hF : ∀ e i, ContDiffOn ℝ ∞ (F e i) (F e i).source)
    (hFi : ∀ e i, ContDiffOn ℝ ∞ (F e i).symm (F e i).target)
    (hfirst : ∀ e i, ∀ s ∈ Icc (0 : ℝ) (r e),
      F e i (s, 0) = H e (sectorParameterEquiv 0 i (s, 0)))
    (hsecond : ∀ e i, ∀ s ∈ Icc (0 : ℝ) (r e),
      F e i (0, s) = H e (sectorParameterEquiv 0 i (0, s)))
    (hchord : ∀ e i, ∀ t : ℝ, F e i ((1 - t) * r e, t * r e) =
      (1 - t) • F e i (r e, 0) + t • F e i (0, r e))
    (hsector : ∀ e i,
      F e i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e} ⊆
        H e '' ((H e).source ∩ (sectorParameterEquiv 0 i) ''
          {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (haxis : ∀ e : Bool, ∀ s : ℝ,
      H e (if vertical e then (0, s) else (s, 0)) = gamma (if e then T - s else s))
    (htip : ∀ e : Bool,
      (if vertical e then ((0 : ℝ), r e) else (r e, 0)) ∈ (H e).source)
    {O : Set AnnulusCoordinates} (hO : IsOpen O)
    (hOarc : gamma '' Icc 0 T ⊆ O) :
    let C (e : Bool) := ⋃ i,
      ⋃ (_ : if positive e then i = (true, true) else i ≠ (true, true)),
        F e i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e}
    (∀ e, C e ⊆ closure U) → Disjoint (C false) (C true) →
    (∀ e : Bool, C e ∩ frontier U ⊆
      (fun s => gamma (if e then T - s else s)) '' Icc 0 (r e) ∪ K) →
    (∀ e : Bool, ∃ W : Set AnnulusCoordinates, IsOpen W ∧
      gamma (if e then T else 0) ∈ W ∧ W ∩ closure U ⊆ C e) →
    ∃ (d : ℝ → AnnulusCoordinates) (n : ℕ) (c : Fin (n + 1) → ℝ)
      (L : Fin n → AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
      (G : Fin n → OpenPartialHomeomorph ℝ ℝ) (f : Fin n → ℝ → ℝ) (ell : ℝ),
      0 < n ∧ StrictMono c ∧ c 0 = r false ∧ c (Fin.last n) = T - r true ∧ 0 < ell ∧
      ∃ B : ∀ i : Fin n,
        ObliqueBandFaces
          (collarParameterEquiv.trans (L i).symm).toHomeomorph.toOpenPartialHomeomorph
          (f i) (G i (c i.castSucc)) (G i (c i.succ))
          (L i (d (c i.castSucc))).1 (L i (d (c i.castSucc))).2
          (L i (d (c i.succ))).1 (L i (d (c i.succ))).2 ell ell,
        (∀ i, (B i).carrier ⊆ O) ∧
        (∀ i, (B i).lowerArc = gamma '' Icc (c i.castSucc) (c i.succ) ∧
          (B i).leftCut = segment ℝ (gamma (c i.castSucc))
            (gamma (c i.castSucc) + ell • d (c i.castSucc)) ∧
          (B i).rightCut = segment ℝ (gamma (c i.succ))
            (gamma (c i.succ) + ell • d (c i.succ)) ∧
          (B i).carrier ⊆ closure U ∧ (B i).carrier \ (B i).lowerArc ⊆ U) ∧
        (∀ i j : Fin n, i.succ < j.castSucc → Disjoint (B i).carrier (B j).carrier) ∧
        (∀ i j : Fin n, i.succ = j.castSucc →
          (B i).carrier ∩ (B j).carrier = segment ℝ (gamma (c i.succ))
            (gamma (c i.succ) + ell • d (c i.succ))) ∧
        (∀ i, (C false ∪ C true) ∩ (B i).carrier =
          (if c i.castSucc = r false then (B i).leftCut else ∅) ∪
            (if c i.succ = T - r true then (B i).rightCut else ∅)) ∧
        ∀ p ∈ Icc (0 : ℝ) T, ∃ W : Set AnnulusCoordinates,
          IsOpen W ∧ gamma p ∈ W ∧
            W ∩ closure U ⊆ (C false ∪ C true) ∪ ⋃ i, (B i).carrier := by
  classical
  intro C hsub hCC hcontact hcorner
  obtain ⟨d, hpaths, n, c, L, G, f, hn, hc, hcfirst, hclast,
    epsilon, hepsilon, hepsilon1, hbands⟩ :=
    m64Intrinsic_exists_two_corner_arc_bands hg hinj hregular hK havoid hU hV hdisj
      hfU hfV hray r hr hrbound H F positive vertical hsource hF hFi hfirst hsecond
      hchord hsector haxis htip hO hOarc hsub hCC hcontact
  have hrT (e : Bool) : r e < T := by linarith [hr e, hrbound e]
  let selected (e : Bool) := if vertical e then (positive e, true) else (true, positive e)
  have hselectedSub (e : Bool) :
      F e (selected e) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e} ⊆ C e := by
    intro z hz
    refine mem_iUnion.mpr ⟨selected e, mem_iUnion.mpr ⟨?_, hz⟩⟩
    cases hp : positive e <;> cases hv : vertical e <;> simp [selected, hp, hv]
  have hCunion (e : Bool) : C e ⊆ C false ∪ C true := by
    cases e
    · exact subset_union_left
    · exact subset_union_right
  have hshort (e : Bool) := m64Intrinsic_exists_arc_short_cap_band_join_length
    hg (hr e) (hrT e) hinj hregular hK havoid hU hV hdisj hfU (hfV.trans hfU)
      (H e) (F e) (hsource e) (hF e) (hFi e) (hfirst e) (hsecond e)
      (hchord e) (hsector e) (positive e) e (vertical e) (haxis e) (htip e)
      (d (if e then T - r e else r e)) (hsub e)
  choose delta hdelta hshort using hshort
  let ell := min epsilon (min (delta false) (delta true)) / 2
  have hell : 0 < ell := half_pos (lt_min hepsilon (lt_min (hdelta false) (hdelta true)))
  have helleps : ell < epsilon := by
    dsimp [ell]
    linarith [min_le_left epsilon (min (delta false) (delta true))]
  have hell1 : ell ≤ 1 := helleps.le.trans hepsilon1
  have helldelta (e : Bool) : ell ≤ delta e := by
    have hm := min_le_right epsilon (min (delta false) (delta true))
    dsimp [ell]
    cases e
    · linarith [min_le_left (delta false) (delta true), hdelta false]
    · linarith [min_le_right (delta false) (delta true), hdelta true]
  obtain ⟨B, hBO, hB, hsep, hadj, hcapB⟩ :=
    hbands (fun _ => ell) (fun _ => ⟨hell, helleps⟩)
  have hcut (k : Fin (n + 1)) : c k ∈ Icc (r false) (T - r true) := by
    constructor
    · simpa only [hcfirst] using hc.monotone (Fin.zero_le k)
    · simpa only [hclast] using hc.monotone (Fin.le_last k)
  have hlower (i : Fin n) : (B i).lowerArc ⊆ gamma '' Icc 0 T := by
    rw [(hB i).1]
    exact image_mono (Icc_subset_Icc ((hr false).le.trans (hcut i.castSucc).1)
      ((hcut i.succ).2.trans (sub_le_self T (hr true).le)))
  have hbaseB (i : Fin n) (e : Bool) :
      ((B i).endpointEdge e).map 0 = gamma (c (if e then i.succ else i.castSucc)) := by
    cases e
    · rw [m64Intrinsic_band_left_endpoint_zero]
      have h := m64Intrinsic_band_left_cut (L i).symm (B i)
      simp only [Prod.eta, (L i).symm_apply_apply] at h
      exact m64Intrinsic_segment_base_eq_of_same_direction (h.symm.trans (hB i).2.1)
    · rw [m64Intrinsic_band_right_endpoint_zero]
      have h := m64Intrinsic_band_right_cut (L i).symm (B i)
      simp only [Prod.eta, (L i).symm_apply_apply] at h
      exact m64Intrinsic_segment_base_eq_of_same_direction (h.symm.trans (hB i).2.2.1)
  have himageB (i : Fin n) (e : Bool) :
      ((B i).endpointEdge e).map '' Icc (0 : ℝ) 1 =
        (fun u : ℝ => gamma (c (if e then i.succ else i.castSucc)) +
          u • d (c (if e then i.succ else i.castSucc))) '' Icc 0 ell := by
    rw [(B i).endpointEdge_image]
    cases e
    · rw [if_neg Bool.false_ne_true, (hB i).2.1]
      exact (m64Intrinsic_ray_image_eq_segment _ _ hell.le).symm
    · rw [if_pos rfl, (hB i).2.2.1]
      exact (m64Intrinsic_ray_image_eq_segment _ _ hell.le).symm
  have hinterB (e : Bool) (i : Fin n) :
      C e ∩ (B i).carrier ⊆ (B i).leftCut ∪ (B i).rightCut := by
    apply (inter_subset_inter_left _ (hCunion e)).trans
    rw [hcapB i]
    split_ifs <;> simp
  let idx (e : Bool) : Fin n := if e then ⟨n - 1, by omega⟩ else ⟨0, hn⟩
  have hendidx (e : Bool) :
      c (if e then (idx e).succ else (idx e).castSucc) = if e then T - r e else r e := by
    cases e
    · exact hcfirst
    · have he : (idx true).succ = Fin.last n := Fin.ext (by dsimp [idx]; omega)
      exact he ▸ hclast
  have hjoin (e : Bool) : ∃ W : Set AnnulusCoordinates, IsOpen W ∧
      gamma (if e then T - r e else r e) ∈ W ∧
      W ∩ closure U ⊆ (C false ∪ C true) ∪ ⋃ i, (B i).carrier := by
    let i := idx e
    have hbase' : ((B i).endpointEdge e).map 0 =
        gamma (if e then T - r e else r e) :=
      (hbaseB i e).trans (congrArg gamma (hendidx e))
    have himage' : ((B i).endpointEdge e).map '' Icc (0 : ℝ) 1 =
        (fun u : ℝ => gamma (if e then T - r e else r e) +
          u • d (if e then T - r e else r e)) '' Icc 0 ell := by
      rw [himageB, hendidx]
    have hcutC : ((B i).endpointEdge e).map '' Icc (0 : ℝ) 1 ⊆ C e := by
      rw [himage']
      rintro z ⟨u, hu, rfl⟩
      exact hpaths e u ⟨hu.1, hu.2.trans hell1⟩
    obtain ⟨W, hW, hpW, hcover⟩ := hshort e ell hell (helldelta e)
      (L i).symm (f i) _ _ _ _ _ _ _ _ (B i) hbase' himage' hcutC (hinterB e i)
        (hB i).2.2.2.1 (hB i).2.2.2.2 (hlower i)
    exact ⟨W, hW, hpW, hcover.trans (union_subset_union
      ((hselectedSub e).trans (hCunion e)) (subset_iUnion (fun j => (B j).carrier) i))⟩
  have hradial (e : Bool) (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) (r e)) :
      ∃ W : Set AnnulusCoordinates, IsOpen W ∧
        gamma (if e then T - s else s) ∈ W ∧
          W ∩ closure U ⊆ (C false ∪ C true) ∪ ⋃ i, (B i).carrier := by
    have hcapAxis : ∀ t ∈ Icc (0 : ℝ) (r e),
        F e (selected e) (if vertical e then (0, t) else (t, 0)) =
          gamma (if e then T - t else t) := by
      intro t ht
      cases hv : vertical e
      · calc
          F e (selected e) (t, 0) = H e (t, 0) := by
            simpa [selected, hv, sectorParameterEquiv_apply] using
              hfirst e (true, positive e) t ht
          _ = gamma (if e then T - t else t) := by simpa [hv] using haxis e t
      · calc
          F e (selected e) (0, t) = H e (0, t) := by
            simpa [selected, hv, sectorParameterEquiv_apply] using
              hsecond e (positive e, true) t ht
          _ = gamma (if e then T - t else t) := by simpa only [hv, if_true] using haxis e t
    obtain ⟨W, hW, hpW, hcover⟩ := m64Intrinsic_arc_chosen_cap_covers_original_axis
      hg (hr e) (hrT e) hinj hregular hK havoid hU hV hdisj hfU (hfV.trans hfU)
        (F e (selected e)) (hsource e _) (hF e _) (hFi e _)
        ((hselectedSub e).trans (hsub e)) e (vertical e) hcapAxis s hs
    exact ⟨W, hW, hpW,
      hcover.trans (((hselectedSub e).trans (hCunion e)).trans subset_union_left)⟩
  refine ⟨d, n, c, L, G, f, ell, hn, hc, hcfirst, hclast,
    hell, B, hBO, hB, hsep, hadj, hcapB, ?_⟩
  intro p hp
  by_cases hp0 : p = 0
  · subst p
    obtain ⟨W, hW, hpW, hcover⟩ := hcorner false
    exact ⟨W, hW, hpW, hcover.trans ((hCunion false).trans subset_union_left)⟩
  by_cases hpT : p = T
  · subst p
    obtain ⟨W, hW, hpW, hcover⟩ := hcorner true
    exact ⟨W, hW, hpW, hcover.trans ((hCunion true).trans subset_union_left)⟩
  by_cases hleft : p < r false
  · exact hradial false p ⟨lt_of_le_of_ne hp.1 (Ne.symm hp0), hleft⟩
  by_cases hright : T - r true < p
  · obtain ⟨W, hW, hpW, hcover⟩ := hradial true (T - p)
      ⟨sub_pos.mpr (lt_of_le_of_ne hp.2 hpT), by linarith⟩
    refine ⟨W, hW, ?_, hcover⟩
    simpa only [if_true, sub_sub_cancel] using hpW
  by_cases hpr : p = r false
  · subst p
    exact hjoin false
  by_cases hptr : p = T - r true
  · subst p
    exact hjoin true
  obtain ⟨W, hW, hpW, hcover⟩ := m64Intrinsic_arc_trimmed_band_chain_covers_region hg
    (hr false) (sub_lt_self T (hr true)) hinj hregular hK havoid hU hV hdisj hfU
      (hfV.trans hfU) c hc hcfirst hclast L G f (fun _ => ell) B
      (fun i => ⟨(hB i).1, (hB i).2.1, (hB i).2.2.1⟩)
      (fun i => (hB i).2.2.2) hadj p
      ⟨lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hpr),
        lt_of_le_of_ne (le_of_not_gt hright) hptr⟩
  exact ⟨W, hW, hpW, hcover.trans subset_union_right⟩

end PoincareConjecture
