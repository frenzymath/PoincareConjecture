import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_AttachedMiddleBands
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcCapChordSign
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcCapSeparators
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcCornerContacts
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandPhysicalSeparator
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_BandEndpointGeometry
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






theorem m64Intrinsic_exists_cap_patch_arc_bands
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T r b : ℝ}
    (hr : 0 < r) (hrT : r < T) (hb : b ∈ Ioo (0 : ℝ) T)
    (terminal : Bool) (hgap : (if terminal then b else r) < if terminal then T - r else b)
    (hinj : InjOn gamma (Icc 0 T))
    (hregular : ∀ t ∈ Ioo (0 : ℝ) T, deriv gamma t ≠ 0)
    {K U V Z O : Set AnnulusCoordinates} (hK : IsCompact K)
    (havoidK : ∀ t ∈ Ioo (0 : ℝ) T, gamma t ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : frontier U = gamma '' Icc 0 T ∪ K) (hfV : frontier V = frontier U)
    (hray : ∀ t ∈ Ioo (0 : ℝ) T, ∀ᶠ z in 𝓝[>] (0 : ℝ),
      gamma t + z • quarterTurn (deriv gamma t) ∈ U)
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (F : Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (positive vertical : Bool)
    (hsource : ∀ i,
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ (F i).source)
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (F i).source)
    (hFi : ∀ i, ContDiffOn ℝ ∞ (F i).symm (F i).target)
    (hfirst : ∀ i, ∀ s ∈ Icc (0 : ℝ) r,
      F i (s, 0) = H (sectorParameterEquiv 0 i (s, 0)))
    (hsecond : ∀ i, ∀ s ∈ Icc (0 : ℝ) r,
      F i (0, s) = H (sectorParameterEquiv 0 i (0, s)))
    (hchord : ∀ i, ∀ t : ℝ, F i ((1 - t) * r, t * r) =
      (1 - t) • F i (r, 0) + t • F i (0, r))
    (hsector : ∀ i,
      F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆
        H '' (H.source ∩ (sectorParameterEquiv 0 i) ''
          {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (haxis : ∀ s : ℝ, H (if vertical then (0, s) else (s, 0)) =
      gamma (if terminal then T - s else s))
    (htip : (if vertical then ((0 : ℝ), r) else (r, 0)) ∈ H.source)
    (L : (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates)
    {f : ℝ → ℝ} {a0 a1 ua wa ub wb ra rb : ℝ} (ha01 : a0 < a1)
    (B : ObliqueBandFaces
      (collarParameterEquiv.trans L).toHomeomorph.toOpenPartialHomeomorph
      f a0 a1 ua wa ub wb ra rb)
    (hbase : L (if terminal then a1 else a0, f (if terminal then a1 else a0)) = gamma b)
    (htangent : ∃ speed : ℝ, 0 < speed ∧
      deriv gamma b = speed • L (1, deriv f (if terminal then a1 else a0)))
    (htrans : 0 < inner ℝ (quarterTurn (deriv gamma b))
      (if terminal then L (ub, wb) else L (ua, wa)))
    (hlower : B.lowerArc = if terminal then gamma '' Icc 0 b else gamma '' Icc b T)
    (hBopen : B.carrier \ B.lowerArc ⊆ U)
    (hZ : IsClosed Z) (hZfront : Z ∩ frontier U ⊆ K)
    (hO : IsOpen O)
    (haxisO : gamma '' Icc (if terminal then b else r) (if terminal then T - r else b) ⊆ O) :
    let selected := if vertical then (positive, true) else (true, positive)
    let vC := if vertical then F selected (r, 0) - F selected (0, r)
      else F selected (0, r) - F selected (r, 0)
    let rho := if terminal then rb else ra
    let w := if terminal then L (ub, wb) else L (ua, wa)
    let C := ⋃ i, ⋃ (_ : if positive then i = (true, true) else i ≠ (true, true)),
      F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
    let P := B.carrier ∪ Z
    C ⊆ closure U → Disjoint C P →
    C ∩ frontier U ⊆ (fun s => gamma (if terminal then T - s else s)) '' Icc 0 r ∪ K →
    (∃ W : Set AnnulusCoordinates, IsOpen W ∧
      gamma (if terminal then T else 0) ∈ W ∧ W ∩ closure U ⊆ C) →
    ∃ d : ℝ → AnnulusCoordinates,
      d (if terminal then T - r else r) = vC ∧ d b = rho • w ∧
      (∀ z ∈ Icc (0 : ℝ) 1,
        gamma (if terminal then T - r else r) +
          z • d (if terminal then T - r else r) ∈ C) ∧
      (∀ z ∈ Icc (0 : ℝ) 1, gamma b + z • d b ∈ P) ∧
      ∃ (n : ℕ) (c : Fin (n + 1) → ℝ)
        (R : Fin n → AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
        (G : Fin n → OpenPartialHomeomorph ℝ ℝ) (g : Fin n → ℝ → ℝ),
        0 < n ∧ StrictMono c ∧ c 0 = (if terminal then b else r) ∧
        c (Fin.last n) = (if terminal then T - r else b) ∧
        ∃ epsilon > 0, epsilon ≤ 1 ∧
          ∀ lengths : Fin (n + 1) → ℝ, (∀ k, lengths k ∈ Ioo (0 : ℝ) epsilon) →
            ∃ D : ∀ i : Fin n,
              ObliqueBandFaces
                (collarParameterEquiv.trans (R i).symm).toHomeomorph.toOpenPartialHomeomorph
                (g i) (G i (c i.castSucc)) (G i (c i.succ))
                (R i (d (c i.castSucc))).1 (R i (d (c i.castSucc))).2
                (R i (d (c i.succ))).1 (R i (d (c i.succ))).2
                (lengths i.castSucc) (lengths i.succ),
              (∀ i, (D i).carrier ⊆ O) ∧
              (∀ i, (D i).lowerArc = gamma '' Icc (c i.castSucc) (c i.succ) ∧
                (D i).leftCut = segment ℝ (gamma (c i.castSucc))
                  (gamma (c i.castSucc) + lengths i.castSucc • d (c i.castSucc)) ∧
                (D i).rightCut = segment ℝ (gamma (c i.succ))
                  (gamma (c i.succ) + lengths i.succ • d (c i.succ)) ∧
                (D i).carrier ⊆ closure U ∧ (D i).carrier \ (D i).lowerArc ⊆ U) ∧
              (∀ i j : Fin n, i.succ < j.castSucc → Disjoint (D i).carrier (D j).carrier) ∧
              (∀ i j : Fin n, i.succ = j.castSucc →
                (D i).carrier ∩ (D j).carrier = segment ℝ (gamma (c i.succ))
                  (gamma (c i.succ) + lengths i.succ • d (c i.succ))) ∧
              (∀ i, (C ∪ P) ∩ (D i).carrier =
                (if c i.castSucc = (if terminal then b else r) then (D i).leftCut else ∅) ∪
                  (if c i.succ = (if terminal then T - r else b) then (D i).rightCut else ∅)) ∧
              ∀ p ∈ (if terminal then Ioc b T else Ico 0 b),
                ∃ W : Set AnnulusCoordinates, IsOpen W ∧ gamma p ∈ W ∧
                  W ∩ closure U ⊆ C ∪ ⋃ i, (D i).carrier := by
  classical
  intro selected vC rho w C P hCsub hCP hCfront hcorner
  let a := if terminal then b else r
  let q := if terminal then T - r else b
  let cap := if terminal then T - r else r
  have ha : 0 < a := by cases terminal <;> first | exact hr | exact hb.1
  have hq : q < T := by cases terminal <;> first | exact hb.2 | exact sub_lt_self T hr
  have hcap : cap ∈ Ioo (0 : ℝ) T := by
    cases terminal
    · exact ⟨hr, hrT⟩
    · exact ⟨sub_pos.mpr hrT, sub_lt_self T hr⟩
  have hcb : cap ≠ b := by
    cases terminal
    · exact ne_of_lt hgap
    · exact ne_of_gt hgap
  have hrho : 0 < rho := by
    cases terminal
    · exact B.left_length_pos
    · exact B.right_length_pos
  have hCclosed : IsClosed C := by
    apply IsCompact.isClosed
    apply isCompact_iUnion
    intro i
    apply isCompact_iUnion
    intro _
    exact m64Intrinsic_cap_isCompact (F i) (hsource i)
  have hPclosed : IsClosed P := B.isClosed_carrier.union hZ
  have hfrontPoint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : gamma t ∈ frontier U := by
    rw [hfront]
    exact Or.inl ⟨t, ht, rfl⟩
  have hZavoid (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) : gamma t ∉ Z :=
    fun hz => havoidK t ht (hZfront ⟨hz, hfrontPoint t (Ioo_subset_Icc_self ht)⟩)
  have hselected : if positive then selected = (true, true) else selected ≠ (true, true) := by
    cases vertical <;> cases positive <;> simp [selected]
  have hselectedSub :
      F selected '' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ r} ⊆ C :=
    fun _ hz => mem_iUnion.mpr ⟨selected, mem_iUnion.mpr ⟨hselected, hz⟩⟩
  have hselectedAxis (s : ℝ) (hs : s ∈ Icc (0 : ℝ) r) :
      F selected (if vertical then (0, s) else (s, 0)) =
        gamma (if terminal then T - s else s) := by
    cases hv : vertical
    · calc
        F selected (s, 0) = H (s, 0) := by
          simpa [selected, hv, sectorParameterEquiv_apply] using hfirst (true, positive) s hs
        _ = gamma (if terminal then T - s else s) := by simpa [hv] using haxis s
    · calc
        F selected (0, s) = H (0, s) := by
          simpa [selected, hv, sectorParameterEquiv_apply] using hsecond (positive, true) s hs
        _ = gamma (if terminal then T - s else s) := by simpa only [hv, if_true] using haxis s
  have hvC : 0 < inner ℝ (quarterTurn (deriv gamma cap)) vC :=
    m64Intrinsic_arc_cap_endpoint_chord_sign hg hinj hregular hK havoidK hU hV hUV hfront hfV
      hray hr hrT (F selected) (hsource selected) (hF selected) (hFi selected)
      (hchord selected) (hselectedSub.trans hCsub) terminal vertical hselectedAxis
  have hpathC (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : gamma cap + z • vC ∈ C := by
    apply hselectedSub
    cases hv : vertical
    · refine ⟨((1 - z) * r, z * r),
        ⟨mul_nonneg (sub_nonneg.mpr hz.2) hr.le, mul_nonneg hz.1 hr.le, by dsimp; nlinarith⟩, ?_⟩
      rw [hchord]
      have hbaseC := hselectedAxis r ⟨hr.le, le_rfl⟩
      simp only [hv, Bool.false_eq_true, if_false] at hbaseC
      rw [← hbaseC]
      simp only [vC, hv, Bool.false_eq_true, if_false]
      module
    · refine ⟨(z * r, (1 - z) * r),
        ⟨mul_nonneg hz.1 hr.le, mul_nonneg (sub_nonneg.mpr hz.2) hr.le, by dsimp; nlinarith⟩, ?_⟩
      have he := hchord selected (1 - z)
      simp only [sub_sub_cancel] at he
      rw [he]
      have hbaseC := hselectedAxis r ⟨hr.le, le_rfl⟩
      simp only [hv, if_true] at hbaseC
      rw [← hbaseC]
      simp only [vC, hv, if_true]
      module
  have hpatchCut : (if terminal then B.rightCut else B.leftCut) =
      segment ℝ (gamma b) (gamma b + rho • w) := by
    rw [← hbase]
    cases terminal
    · exact m64Intrinsic_band_left_cut L B
    · exact m64Intrinsic_band_right_cut L B
  have hcutSub : (if terminal then B.rightCut else B.leftCut) ⊆ B.carrier := by
    rw [← B.endpointEdge_image terminal]
    exact (B.endpointEdge_subset_frontier terminal).trans B.isClosed_carrier.frontier_subset
  have hpathP (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : gamma b + z • (rho • w) ∈ P := by
    apply Or.inl
    apply hcutSub
    rw [hpatchCut, ← m64Intrinsic_ray_image_eq_segment (gamma b) w hrho.le]
    refine ⟨z * rho, ⟨mul_nonneg hz.1 hrho.le, by nlinarith [hz.2]⟩, ?_⟩
    rw [smul_smul]
  obtain ⟨ellC, WC, hWC, hpC, hnormC, hkerC, hsepC⟩ :=
    m64Intrinsic_exists_two_arc_cap_union_separator hg hr H F hsource hF hFi hfirst hsecond
      hchord hsector positive terminal vertical haxis htip
  obtain ⟨ellP, WP, hWP, hpP, hkerP, hsignP, hsepP⟩ :=
    m64Intrinsic_exists_band_physical_separator L ha01 B terminal rfl htangent htrans
  have hkerP' : ellP w = 0 := hkerP
  have hPsep : ∀ z ∈ (WP ∩ Zᶜ) ∩ P, ellP (z - gamma b) ≤ 0 := by
    rintro z ⟨⟨hzW, hzZ⟩, hzB | hzZ'⟩
    · simpa only [hbase] using hsepP z ⟨hzB, hzW⟩
    · exact (hzZ hzZ').elim
  obtain ⟨WC', hWC', hpC', hsepC'⟩ := m64Intrinsic_corner_separator_union
    hPclosed hCP (by simpa only [zero_smul, add_zero] using hpathC 0 (by simp))
    hWC hpC ellC hsepC
  obtain ⟨WP', hWP', hpP', hsepP'⟩ := m64Intrinsic_corner_separator_union
    hCclosed hCP.symm (by simpa only [zero_smul, add_zero] using hpathP 0 (by simp))
    (hWP.inter hZ.isOpen_compl) ⟨hbase ▸ hpP, hZavoid b hb⟩ ellP hPsep
  let d : ℝ → AnnulusCoordinates := fun t =>
    if t = cap then vC else if t = b then rho • w else quarterTurn (deriv gamma t)
  have hdC : d cap = vC := by simp only [d, if_pos rfl]
  have hdP : d b = rho • w := by
    change (if b = cap then vC else if b = b then rho • w
      else quarterTurn (deriv gamma b)) = rho • w
    rw [if_neg hcb.symm, if_pos rfl]
  have hd : ∀ t ∈ Icc a q, 0 < inner ℝ (quarterTurn (deriv gamma t)) (d t) := by
    intro t ht
    by_cases hc : t = cap
    · simpa only [hc, hdC] using hvC
    by_cases hp : t = b
    · simpa only [hp, hdP, real_inner_smul_right] using mul_pos hrho htrans
    have hreg := hregular t ⟨ha.trans_le ht.1, ht.2.trans_lt hq⟩
    have hrot : quarterTurn (deriv gamma t) ≠ 0 := by
      intro hz
      exact hreg (quarterTurn.injective (by simpa only [map_zero] using hz))
    simpa only [d, if_neg hc, if_neg hp] using real_inner_self_pos.mpr hrot
  have havoid : ∀ t ∈ Ioo a q, gamma t ∉ C ∪ P := by
    intro t ht hmem
    have ht' : t ∈ Ioo (0 : ℝ) T := ⟨ha.trans ht.1, ht.2.trans hq⟩
    rcases hmem with hc | hB | hZ'
    · have hc' := m64Intrinsic_arc_corner_contact_parameter hinj hrT.le hfront ht'
        (havoidK t ht') terminal hCfront hc
      cases terminal
      · exact (not_le_of_gt ht.1) hc'
      · exact (not_le_of_gt ht.2) hc'
    · have hlow : gamma t ∈ B.lowerArc := by
        by_contra hn
        exact (disjoint_frontier_iff_isOpen.mpr hU).le_bot
          ⟨hfrontPoint t (Ioo_subset_Icc_self ht'), hBopen ⟨hB, hn⟩⟩
      rw [hlower] at hlow
      cases terminal
      · obtain ⟨s, hs, heq⟩ := hlow
        have he := hinj ⟨hb.1.le.trans hs.1, hs.2⟩ (Ioo_subset_Icc_self ht') heq
        change r < t ∧ t < b at ht
        linarith [hs.1]
      · obtain ⟨s, hs, heq⟩ := hlow
        have he := hinj ⟨hs.1, hs.2.trans hb.2.le⟩ (Ioo_subset_Icc_self ht') heq
        change b < t ∧ t < T - r at ht
        linarith [hs.2]
    · exact hZavoid t ht' hZ'
  have hpaths : ∀ z ∈ Icc (0 : ℝ) 1,
      gamma a + z • d a ∈ C ∪ P ∧ gamma q + z • d q ∈ C ∪ P := by
    intro z hz
    cases terminal
    · exact ⟨Or.inl (hdC ▸ hpathC z hz), Or.inr (hdP ▸ hpathP z hz)⟩
    · exact ⟨Or.inr (hdP ▸ hpathP z hz), Or.inl (hdC ▸ hpathC z hz)⟩
  have hpathCd (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : gamma cap + z • d cap ∈ C := by
    rw [hdC]
    exact hpathC z hz
  have hcutA : (if terminal then ellP else ellC) (d a) = 0 := by
    cases terminal
    · change ellC (d cap) = 0
      rw [hdC]
      exact hkerC
    · change ellP (d b) = 0
      rw [hdP, map_smul, hkerP', smul_zero]
  have hcutB : (if terminal then ellC else ellP) (d q) = 0 := by
    cases terminal
    · change ellP (d b) = 0
      rw [hdP, map_smul, hkerP', smul_zero]
    · change ellC (d cap) = 0
      rw [hdC]
      exact hkerC
  have htA : 0 < (if terminal then ellP else ellC) (deriv gamma a) := by
    cases terminal
    · change 0 < ellC (deriv gamma r)
      have hn : ellC (deriv gamma r) = 1 := hnormC
      linarith
    · exact hsignP
  have htB : (if terminal then ellC else ellP) (deriv gamma q) < 0 := by
    cases terminal
    · exact hsignP
    · change ellC (deriv gamma (T - r)) < 0
      have hn : ellC (deriv gamma (T - r)) = -1 := hnormC
      linarith
  obtain ⟨n, c, R, G, g, hn, hc, hcfirst, hclast, epsilon, hepsilon, hepsilon1, hbands⟩ :=
    m64Intrinsic_exists_attached_middle_bands hg ha hgap hq hinj hregular hK havoidK
      hU hV hUV hfront hfV hray d hd (hCclosed.union hPclosed) havoid hpaths
      (if terminal then ellP else ellC) (if terminal then ellC else ellP)
      hcutA hcutB htA htB
      (WA := if terminal then WP' else WC') (WB := if terminal then WC' else WP')
      (by cases terminal <;> assumption) (by cases terminal <;> assumption)
      (by cases terminal <;> assumption) (by cases terminal <;> assumption)
      (by
        intro z hz
        cases terminal
        · exact hsepC' z ⟨hz.2, hz.1⟩
        · exact hsepP' z ⟨hz.2, hz.1.elim Or.inr Or.inl⟩)
      (by
        intro z hz
        cases terminal
        · exact hsepP' z ⟨hz.2, hz.1.elim Or.inr Or.inl⟩
        · exact hsepC' z ⟨hz.2, hz.1⟩) hO haxisO
  obtain ⟨delta, hdelta, hshort⟩ := m64Intrinsic_exists_arc_short_cap_band_join_length
    hg hr hrT hinj hregular hK havoidK hU hV hUV hfront (hfV.trans hfront)
      H F hsource hF hFi hfirst hsecond hchord hsector positive terminal vertical
      haxis htip (d cap) hCsub
  refine ⟨d, hdC, hdP, hpathCd, ?_, n, c, R, G, g, hn, hc, hcfirst, hclast,
    min epsilon delta, lt_min hepsilon hdelta, (min_le_left _ _).trans hepsilon1, ?_⟩
  · intro z hz
    simpa only [hdP] using hpathP z hz
  intro lengths hlengths
  have hsmall (k : Fin (n + 1)) : lengths k ∈ Ioo (0 : ℝ) epsilon :=
    ⟨(hlengths k).1, (hlengths k).2.trans_le (min_le_left _ _)⟩
  obtain ⟨D, hDO, hD, hsepD, hadjD, hCD⟩ := hbands lengths hsmall
  have hcut (k : Fin (n + 1)) : c k ∈ Icc a q := by
    constructor
    · simpa only [hcfirst] using hc.monotone (Fin.zero_le k)
    · simpa only [hclast] using hc.monotone (Fin.le_last k)
  have hlowerD (i : Fin n) : (D i).lowerArc ⊆ gamma '' Icc 0 T := by
    rw [(hD i).1]
    exact image_mono (Icc_subset_Icc (ha.le.trans (hcut i.castSucc).1)
      ((hcut i.succ).2.trans hq.le))
  have hbaseD (i : Fin n) (e : Bool) :
      ((D i).endpointEdge e).map 0 = gamma (c (if e then i.succ else i.castSucc)) := by
    cases e
    · rw [m64Intrinsic_band_left_endpoint_zero]
      have h := m64Intrinsic_band_left_cut (R i).symm (D i)
      simp only [Prod.eta, (R i).symm_apply_apply] at h
      exact m64Intrinsic_segment_base_eq_of_same_direction (h.symm.trans (hD i).2.1)
    · rw [m64Intrinsic_band_right_endpoint_zero]
      have h := m64Intrinsic_band_right_cut (R i).symm (D i)
      simp only [Prod.eta, (R i).symm_apply_apply] at h
      exact m64Intrinsic_segment_base_eq_of_same_direction (h.symm.trans (hD i).2.2.1)
  have himageD (i : Fin n) (e : Bool) :
      ((D i).endpointEdge e).map '' Icc (0 : ℝ) 1 =
        (fun u : ℝ => gamma (c (if e then i.succ else i.castSucc)) +
          u • d (c (if e then i.succ else i.castSucc))) ''
            Icc 0 (lengths (if e then i.succ else i.castSucc)) := by
    rw [(D i).endpointEdge_image]
    cases e
    · rw [if_neg Bool.false_ne_true, (hD i).2.1]
      exact (m64Intrinsic_ray_image_eq_segment _ _ (hsmall _).1.le).symm
    · rw [if_pos rfl, (hD i).2.2.1]
      exact (m64Intrinsic_ray_image_eq_segment _ _ (hsmall _).1.le).symm
  have hinterC (i : Fin n) : C ∩ (D i).carrier ⊆ (D i).leftCut ∪ (D i).rightCut := by
    apply (inter_subset_inter_left _ (subset_union_left : C ⊆ C ∪ P)).trans
    rw [hCD i]
    split_ifs <;> simp
  let idx : Fin n := if terminal then ⟨n - 1, by omega⟩ else ⟨0, hn⟩
  let k : Fin (n + 1) := if terminal then idx.succ else idx.castSucc
  have hk : c k = cap := by
    cases terminal
    · exact hcfirst
    · have he : k = Fin.last n := Fin.ext (by dsimp [k, idx]; omega)
      exact he ▸ hclast
  have hjoin : ∃ W : Set AnnulusCoordinates, IsOpen W ∧ gamma cap ∈ W ∧
      W ∩ closure U ⊆ C ∪ ⋃ i, (D i).carrier := by
    have hbase' : ((D idx).endpointEdge terminal).map 0 = gamma cap :=
      (hbaseD idx terminal).trans (congrArg gamma hk)
    have himage' : ((D idx).endpointEdge terminal).map '' Icc (0 : ℝ) 1 =
        (fun u : ℝ => gamma cap + u • d cap) '' Icc 0 (lengths k) := by
      rw [himageD]
      change (fun u : ℝ => gamma (c k) + u • d (c k)) '' Icc 0 (lengths k) = _
      rw [hk]
    have hcutC : ((D idx).endpointEdge terminal).map '' Icc (0 : ℝ) 1 ⊆ C := by
      rw [himage']
      rintro z ⟨u, hu, rfl⟩
      exact hpathCd u ⟨hu.1, hu.2.trans ((hsmall k).2.le.trans hepsilon1)⟩
    obtain ⟨W, hW, hpW, hcover⟩ := hshort (lengths k) (hlengths k).1
      ((hlengths k).2.le.trans (min_le_right _ _))
      (R idx).symm (g idx) _ _ _ _ _ _ _ _ (D idx) hbase' himage' hcutC
      (hinterC idx) (hD idx).2.2.2.1 (hD idx).2.2.2.2 (hlowerD idx)
    exact ⟨W, hW, hpW, hcover.trans
      (union_subset_union hselectedSub (subset_iUnion (fun i => (D i).carrier) idx))⟩
  have hradial (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) r) :
      ∃ W : Set AnnulusCoordinates, IsOpen W ∧
        gamma (if terminal then T - s else s) ∈ W ∧
          W ∩ closure U ⊆ C ∪ ⋃ i, (D i).carrier := by
    obtain ⟨W, hW, hpW, hcover⟩ := m64Intrinsic_arc_chosen_cap_covers_original_axis
      hg hr hrT hinj hregular hK havoidK hU hV hUV hfront (hfV.trans hfront)
        (F selected) (hsource selected) (hF selected) (hFi selected)
        (hselectedSub.trans hCsub) terminal vertical hselectedAxis s hs
    exact ⟨W, hW, hpW, hcover.trans (hselectedSub.trans subset_union_left)⟩
  have hmiddle (p : ℝ) (hp : p ∈ Ioo a q) :
      ∃ W : Set AnnulusCoordinates, IsOpen W ∧ gamma p ∈ W ∧
        W ∩ closure U ⊆ C ∪ ⋃ i, (D i).carrier := by
    obtain ⟨W, hW, hpW, hcover⟩ := m64Intrinsic_arc_trimmed_band_chain_covers_region hg
      ha hq hinj hregular hK havoidK hU hV hUV hfront (hfV.trans hfront)
        c hc hcfirst hclast R G g lengths D
        (fun i => ⟨(hD i).1, (hD i).2.1, (hD i).2.2.1⟩)
        (fun i => (hD i).2.2.2) hadjD p hp
    exact ⟨W, hW, hpW, hcover.trans subset_union_right⟩
  refine ⟨D, hDO, hD, hsepD, hadjD, hCD, ?_⟩
  intro p hp
  cases terminal
  · change p ∈ Ico 0 b at hp
    by_cases hp0 : p = 0
    · subst p
      obtain ⟨W, hW, hpW, hcover⟩ := hcorner
      exact ⟨W, hW, hpW, hcover.trans subset_union_left⟩
    by_cases hpr : p < r
    · exact hradial p ⟨lt_of_le_of_ne hp.1 (Ne.symm hp0), hpr⟩
    by_cases hpr' : p = r
    · subst p
      exact hjoin
    exact hmiddle p ⟨lt_of_le_of_ne (le_of_not_gt hpr) (Ne.symm hpr'), hp.2⟩
  · change p ∈ Ioc b T at hp
    by_cases hpT : p = T
    · subst p
      obtain ⟨W, hW, hpW, hcover⟩ := hcorner
      exact ⟨W, hW, hpW, hcover.trans subset_union_left⟩
    by_cases hpr : T - r < p
    · obtain ⟨W, hW, hpW, hcover⟩ := hradial (T - p)
        ⟨sub_pos.mpr (lt_of_le_of_ne hp.2 hpT), by linarith⟩
      exact ⟨W, hW, by simpa only [if_true, sub_sub_cancel] using hpW, hcover⟩
    by_cases hpr' : p = T - r
    · subst p
      exact hjoin
    exact hmiddle p ⟨hp.1, lt_of_le_of_ne (le_of_not_gt hpr) hpr'⟩

end PoincareConjecture
