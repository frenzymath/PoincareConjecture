import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_AttachedReturnBands
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ShortBandJoinCoverage
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RetainedCapRadialCoverage
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TrimmedBandCoverage

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture

theorem m64Intrinsic_exists_covered_return_bands
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ} (hT : 0 < T)
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    (hind : LinearIndependent ℝ
      (![deriv gamma 0, -deriv gamma T] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T)
    (hray : ∀ t ∈ Ioo (0 : ℝ) T, ∀ᶠ z in 𝓝[>] (0 : ℝ),
      gamma t + z • quarterTurn (deriv gamma t) ∈ U) :
    ∃ (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) (r : ℝ)
      (F : Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
      (positive : Bool) (d : ℝ → AnnulusCoordinates),
      let caps (i : Bool × Bool) :=
        F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
      let C := ⋃ i, ⋃ (_ : if positive then i = (true, true) else i ≠ (true, true)), caps i
      0 < r ∧ r ≤ T / 3 ∧ (0 : ℝ × ℝ) ∈ H.source ∧ H 0 = gamma 0 ∧
      ContDiffOn ℝ ∞ H H.source ∧ ContDiffOn ℝ ∞ H.symm H.target ∧
      (∀ s : ℝ, H (s, 0) = gamma s) ∧
      (∀ s : ℝ, H (0, s) = gamma (T - s)) ∧
      (∀ i : Bool × Bool, ∀ s ∈ Icc (0 : ℝ) r,
        sectorParameterEquiv 0 i (s, 0) ∈ H.source ∧
        sectorParameterEquiv 0 i (0, s) ∈ H.source) ∧
      (∀ i,
        {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ (F i).source ∧
        (F i).target ⊆ H.target ∧
        ContDiffOn ℝ ∞ (F i) (F i).source ∧
        ContDiffOn ℝ ∞ (F i).symm (F i).target ∧
        (∀ s ∈ Icc (0 : ℝ) r, F i (s, 0) = H (sectorParameterEquiv 0 i (s, 0))) ∧
        (∀ s ∈ Icc (0 : ℝ) r, F i (0, s) = H (sectorParameterEquiv 0 i (0, s))) ∧
        (∀ t : ℝ, F i ((1 - t) * r, t * r) =
          (1 - t) • F i (r, 0) + t • F i (0, r)) ∧
        caps i ⊆ H '' (H.source ∩ (sectorParameterEquiv 0 i) ''
          {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) ∧
        caps i ∩ H '' (H.source ∩ {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0}) =
          H '' ((sectorParameterEquiv 0 i) ''
            ((Icc (0 : ℝ) r ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) r)))) ∧
      IsCompact C ∧ C ⊆ closure U ∧
      C ∩ gamma '' Icc 0 T = gamma '' Icc 0 r ∪ gamma '' Icc (T - r) T ∧
      ∃ (n : ℕ) (c : Fin (n + 1) → ℝ)
        (L : Fin n → AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
        (G : Fin n → OpenPartialHomeomorph ℝ ℝ) (f : Fin n → ℝ → ℝ) (ell : ℝ),
        0 < n ∧ StrictMono c ∧ c 0 = r ∧ c (Fin.last n) = T - r ∧ 0 < ell ∧
        ∃ B : ∀ i : Fin n,
          ObliqueBandFaces
            (collarParameterEquiv.trans (L i).symm).toHomeomorph.toOpenPartialHomeomorph
            (f i) (G i (c i.castSucc)) (G i (c i.succ))
            (L i (d (c i.castSucc))).1 (L i (d (c i.castSucc))).2
            (L i (d (c i.succ))).1 (L i (d (c i.succ))).2 ell ell,
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
          (∀ i, C ∩ (B i).carrier =
            (if c i.castSucc = r then (B i).leftCut else ∅) ∪
              (if c i.succ = T - r then (B i).rightCut else ∅)) ∧
          ∀ p ∈ Icc (0 : ℝ) T, ∃ W : Set AnnulusCoordinates,
            IsOpen W ∧ gamma p ∈ W ∧ W ∩ closure U ⊆ C ∪ ⋃ i, (B i).carrier := by
  classical
  obtain ⟨H, r, F, W0, positive, d, hr, hrbound, h0, hbase, hH, hHi, haxis, haxis',
    hsmall, hF, hW0, hpW0, hcompact, hsub, hcover0, hcontact,
    n, c, L, G, f, hn, hc, hfirst, hlast, epsilon, hepsilon, _, hbands⟩ :=
    m64Intrinsic_exists_cap_attached_return_bands hg hT hend hinj hregular hind
      hU hV hdisj hfU hfV hray
  let caps (i : Bool × Bool) :=
    F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
  let C := ⋃ i, ⋃ (_ : if positive then i = (true, true) else i ≠ (true, true)), caps i
  have hrT : r < T := by linarith
  have hselectedSub (terminal : Bool) :
      caps (if terminal then (positive, true) else (true, positive)) ⊆ C := by
    intro z hz
    refine mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨?_, hz⟩⟩
    cases positive <;> cases terminal <;> simp
  have hshort (terminal : Bool) := m64Intrinsic_exists_short_cap_band_join_length
    hg hr hrT hend hinj hregular hU hV hdisj hfU hfV H hbase haxis haxis' F
      (fun i => (hF i).1) (fun i => (hF i).2.2.1) (fun i => (hF i).2.2.2.1)
      (fun i => (hF i).2.2.2.2.1) (fun i => (hF i).2.2.2.2.2.1)
      (fun i => (hF i).2.2.2.2.2.2.1) (fun i => (hF i).2.2.2.2.2.2.2.1)
      positive terminal (d (if terminal then T - r else r)) hsub
  choose delta hdelta hshort using hshort
  let ell := min epsilon (min (delta false) (delta true)) / 2
  have hell : 0 < ell := half_pos (lt_min hepsilon (lt_min (hdelta false) (hdelta true)))
  have helleps : ell < epsilon := by
    dsimp [ell]
    linarith [min_le_left epsilon (min (delta false) (delta true))]
  have helldelta (terminal : Bool) : ell ≤ delta terminal := by
    have hm := min_le_right epsilon (min (delta false) (delta true))
    dsimp [ell]
    cases terminal
    · linarith [min_le_left (delta false) (delta true), hdelta false]
    · linarith [min_le_right (delta false) (delta true), hdelta true]
  obtain ⟨B, hB, hsep, hadj, hcapB⟩ := hbands (fun _ => ell) (fun _ => ⟨hell, helleps⟩)
  have hcut (k : Fin (n + 1)) : c k ∈ Icc r (T - r) := by
    constructor
    · simpa only [hfirst] using hc.monotone (Fin.zero_le k)
    · simpa only [hlast] using hc.monotone (Fin.le_last k)
  have hlower (i : Fin n) : (B i).lowerArc ⊆ gamma '' Icc 0 T := by
    rw [(hB i).1]
    exact image_mono (Icc_subset_Icc (hr.le.trans (hcut i.castSucc).1)
      ((hcut i.succ).2.trans (sub_le_self T hr.le)))
  have hbaseB (i : Fin n) (terminal : Bool) :
      ((B i).endpointEdge terminal).map 0 =
        gamma (c (if terminal then i.succ else i.castSucc)) := by
    cases terminal
    · rw [m64Intrinsic_band_left_endpoint_zero]
      have h := m64Intrinsic_band_left_cut (L i).symm (B i)
      simp only [Prod.eta, (L i).symm_apply_apply] at h
      exact m64Intrinsic_segment_base_eq_of_same_direction (h.symm.trans (hB i).2.1)
    · rw [m64Intrinsic_band_right_endpoint_zero]
      have h := m64Intrinsic_band_right_cut (L i).symm (B i)
      simp only [Prod.eta, (L i).symm_apply_apply] at h
      exact m64Intrinsic_segment_base_eq_of_same_direction (h.symm.trans (hB i).2.2.1)
  have himageB (i : Fin n) (terminal : Bool) :
      ((B i).endpointEdge terminal).map '' Icc (0 : ℝ) 1 =
        (fun u : ℝ => gamma (c (if terminal then i.succ else i.castSucc)) +
          u • d (c (if terminal then i.succ else i.castSucc))) '' Icc 0 ell := by
    rw [(B i).endpointEdge_image]
    cases terminal
    · rw [if_neg Bool.false_ne_true, (hB i).2.1]
      exact (m64Intrinsic_ray_image_eq_segment _ _ hell.le).symm
    · rw [if_pos rfl, (hB i).2.2.1]
      exact (m64Intrinsic_ray_image_eq_segment _ _ hell.le).symm
  have hinterB (i : Fin n) : C ∩ (B i).carrier ⊆ (B i).leftCut ∪ (B i).rightCut := by
    rw [hcapB i]
    split_ifs <;> simp
  let idx (terminal : Bool) : Fin n := if terminal then ⟨n - 1, by omega⟩ else ⟨0, hn⟩
  have hendidx (terminal : Bool) :
      c (if terminal then (idx terminal).succ else (idx terminal).castSucc) =
        if terminal then T - r else r := by
    cases terminal
    · exact hfirst
    · have he : (idx true).succ = Fin.last n := Fin.ext (by dsimp [idx]; omega)
      exact he ▸ hlast
  have hjoin (terminal : Bool) : ∃ W : Set AnnulusCoordinates, IsOpen W ∧
      gamma (if terminal then T - r else r) ∈ W ∧
      W ∩ closure U ⊆ C ∪ ⋃ i, (B i).carrier := by
    let i := idx terminal
    have hbase' : ((B i).endpointEdge terminal).map 0 =
        gamma (if terminal then T - r else r) := (hbaseB i terminal).trans
          (congrArg gamma (hendidx terminal))
    have himage' : ((B i).endpointEdge terminal).map '' Icc (0 : ℝ) 1 =
        (fun u : ℝ => gamma (if terminal then T - r else r) +
          u • d (if terminal then T - r else r)) '' Icc 0 ell := by
      rw [himageB, hendidx]
    have hcutC : ((B i).endpointEdge terminal).map '' Icc (0 : ℝ) 1 ⊆ C := by
      intro z hz
      have hzint : z ∈ C ∩ (B i).carrier := by
        rw [hcapB i]
        rw [(B i).endpointEdge_image] at hz
        cases terminal
        · left
          have hi := hendidx false
          change c i.castSucc = r at hi
          simpa only [Bool.false_eq_true, ↓reduceIte, hi, if_pos rfl] using hz
        · right
          have hi := hendidx true
          change c i.succ = T - r at hi
          simpa only [Bool.false_eq_true, ↓reduceIte, hi, if_pos rfl] using hz
      exact hzint.1
    obtain ⟨W, hW, hpW, hcover⟩ := hshort terminal ell hell (helldelta terminal)
      (L i).symm (f i) _ _ _ _ _ _ _ _ (B i) hbase' himage' hcutC (hinterB i)
        (hB i).2.2.2.1 (hB i).2.2.2.2 (hlower i)
    refine ⟨W, hW, hpW, hcover.trans ?_⟩
    exact union_subset_union (hselectedSub terminal) (subset_iUnion (fun j => (B j).carrier) i)
  have hradial (terminal : Bool) (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) r) :
      ∃ W : Set AnnulusCoordinates, IsOpen W ∧
        gamma (if terminal then T - s else s) ∈ W ∧ W ∩ closure U ⊆ C ∪ ⋃ i, (B i).carrier := by
    let selected := if terminal then (positive, true) else (true, positive)
    have hcapAxis : ∀ t ∈ Icc (0 : ℝ) r,
        F selected (if terminal then (0, t) else (t, 0)) =
          gamma (if terminal then T - t else t) := by
      intro t ht
      cases terminal
      · simpa [selected, sectorParameterEquiv_apply, haxis] using
          (hF (true, positive)).2.2.2.2.1 t ht
      · simpa [selected, sectorParameterEquiv_apply, haxis'] using
          (hF (positive, true)).2.2.2.2.2.1 t ht
    obtain ⟨W, hW, hpW, hcover⟩ := m64Intrinsic_chosen_cap_covers_original_axis
      hg hr hrT hend hinj hregular hU hV hdisj hfU hfV (F selected) (hF selected).1
        (hF selected).2.2.1 (hF selected).2.2.2.1
        ((hselectedSub terminal).trans hsub) terminal hcapAxis s hs
    exact ⟨W, hW, hpW, hcover.trans ((hselectedSub terminal).trans subset_union_left)⟩
  refine ⟨H, r, F, positive, d, hr, hrbound, h0, hbase, hH, hHi, haxis, haxis',
    hsmall, hF, hcompact, hsub, hcontact, n, c, L, G, f, ell, hn, hc, hfirst, hlast,
    hell, B, hB, hsep, hadj, hcapB, ?_⟩
  intro p hp
  by_cases hp0 : p = 0
  · subst p
    exact ⟨W0, hW0, hpW0, hcover0.trans subset_union_left⟩
  by_cases hpT : p = T
  · subst p
    exact ⟨W0, hW0, hend ▸ hpW0, hcover0.trans subset_union_left⟩
  by_cases hleft : p < r
  · exact hradial false p ⟨lt_of_le_of_ne hp.1 (Ne.symm hp0), hleft⟩
  by_cases hright : T - r < p
  · obtain ⟨W, hW, hpW, hcover⟩ := hradial true (T - p)
      ⟨sub_pos.mpr (lt_of_le_of_ne hp.2 hpT), by linarith⟩
    refine ⟨W, hW, ?_, hcover⟩
    simpa only [↓reduceIte, sub_sub_cancel] using hpW
  by_cases hpr : p = r
  · subst p
    exact hjoin false
  by_cases hptr : p = T - r
  · subst p
    exact hjoin true
  obtain ⟨W, hW, hpW, hcover⟩ := m64Intrinsic_trimmed_band_chain_covers_region hg hr
    (sub_lt_self T hr) hend hinj hregular hU hV hdisj hfU hfV c hc hfirst hlast L G f
      (fun _ => ell) B (fun i => ⟨(hB i).1, (hB i).2.1, (hB i).2.2.1⟩)
      (fun i => (hB i).2.2.2) hadj p
      ⟨lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hpr),
        lt_of_le_of_ne (le_of_not_gt hright) hptr⟩
  exact ⟨W, hW, hpW, hcover.trans subset_union_right⟩

end PoincareConjecture
