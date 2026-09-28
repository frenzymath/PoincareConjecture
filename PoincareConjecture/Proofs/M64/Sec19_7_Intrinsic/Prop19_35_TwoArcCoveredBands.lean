import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoCornerCaps
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcBandOppositeNeighborhood







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Matrix
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture





theorem m64Intrinsic_exists_two_arc_covered_bands
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hareg : ∀ t ∈ Ioo (0 : ℝ) A, deriv alpha t ≠ 0)
    (hbreg : ∀ t ∈ Ioo (0 : ℝ) B, deriv beta t ≠ 0)
    (hinter : (alpha '' Icc 0 A) ∩ (beta '' Icc 0 B) ⊆ {alpha 0, alpha A})
    (hbase : beta 0 = alpha 0) (hend : beta B = alpha A)
    (hind0 : LinearIndependent ℝ
      (![deriv alpha 0, deriv beta 0] : Fin 2 → AnnulusCoordinates))
    (hind1 : LinearIndependent ℝ
      (![-deriv alpha A, -deriv beta B] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B)
    (hfV : frontier V = frontier U) :
    ∃ (H : Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) (r : Bool → ℝ)
      (F : Bool → Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
      (W : Bool → Set AnnulusCoordinates) (positive : Bool → Bool),
      let C (e : Bool) (i : Bool × Bool) :=
        F e i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e}
      let D (e : Bool) := ⋃ i,
        ⋃ (_ : if positive e then i = (true, true) else i ≠ (true, true)), C e i
      (∀ e : Bool,
        0 < r e ∧ r e ≤ min A B / 3 ∧ (0 : ℝ × ℝ) ∈ (H e).source ∧
        H e 0 = alpha (if e then A else 0) ∧
        ContDiffOn ℝ ∞ (H e) (H e).source ∧ ContDiffOn ℝ ∞ (H e).symm (H e).target ∧
        (∀ s : ℝ, H e (s, 0) = alpha (if e then A - s else s)) ∧
        (∀ s : ℝ, H e (0, s) = beta (if e then B - s else s)) ∧
        (∀ i : Bool × Bool, ∀ s ∈ Icc (0 : ℝ) (r e),
          sectorParameterEquiv 0 i (s, 0) ∈ (H e).source ∧
          sectorParameterEquiv 0 i (0, s) ∈ (H e).source) ∧
        (∀ q ∈ (H e).source, H e q ∈ frontier U ↔
          (q.1 = 0 ∧ 0 ≤ q.2) ∨ (0 ≤ q.1 ∧ q.2 = 0)) ∧
        (∀ q ∈ (H e).source, H e q ∈ closure U ↔
          if positive e then 0 ≤ q.1 ∧ 0 ≤ q.2 else q.1 ≤ 0 ∨ q.2 ≤ 0) ∧
        (∀ i,
          {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e} ⊆ (F e i).source ∧
          (F e i).target ⊆ (H e).target ∧
          ContDiffOn ℝ ∞ (F e i) (F e i).source ∧
          ContDiffOn ℝ ∞ (F e i).symm (F e i).target ∧
          (∀ s ∈ Icc (0 : ℝ) (r e), F e i (s, 0) = H e (sectorParameterEquiv 0 i (s, 0))) ∧
          (∀ s ∈ Icc (0 : ℝ) (r e), F e i (0, s) = H e (sectorParameterEquiv 0 i (0, s))) ∧
          (∀ t : ℝ, F e i ((1 - t) * r e, t * r e) =
            (1 - t) • F e i (r e, 0) + t • F e i (0, r e)) ∧
          C e i ⊆ H e '' ((H e).source ∩ (sectorParameterEquiv 0 i) ''
            {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) ∧
          C e i ∩ H e '' ((H e).source ∩ {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0}) =
            H e '' ((sectorParameterEquiv 0 i) ''
              ((Icc (0 : ℝ) (r e) ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) (r e))))) ∧
        IsOpen (W e) ∧ alpha (if e then A else 0) ∈ W e ∧
        IsCompact (D e) ∧ D e ⊆ closure U ∧ W e ∩ closure U ⊆ D e ∧
        D e ∩ frontier U =
          (fun s => alpha (if e then A - s else s)) '' Icc 0 (r e) ∪
          (fun s => beta (if e then B - s else s)) '' Icc 0 (r e)) ∧
      Disjoint (D false) (D true) ∧
    ∃ rev0 : Bool,
      let g0 : ℝ → AnnulusCoordinates := fun t => alpha (if rev0 then A - t else t)
      let r0 (e : Bool) := r (if rev0 then !e else e)
      ∃ (d0 : ℝ → AnnulusCoordinates) (n0 : ℕ) (c0 : Fin (n0 + 1) → ℝ)
        (L0 : Fin n0 → AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
        (G0 : Fin n0 → OpenPartialHomeomorph ℝ ℝ) (f0 : Fin n0 → ℝ → ℝ) (ell0 : ℝ),
        0 < n0 ∧ StrictMono c0 ∧ c0 0 = r0 false ∧ c0 (Fin.last n0) = A - r0 true ∧ 0 < ell0 ∧
        ∃ B0 : ∀ i : Fin n0,
          ObliqueBandFaces
            (collarParameterEquiv.trans (L0 i).symm).toHomeomorph.toOpenPartialHomeomorph
            (f0 i) (G0 i (c0 i.castSucc)) (G0 i (c0 i.succ))
            (L0 i (d0 (c0 i.castSucc))).1 (L0 i (d0 (c0 i.castSucc))).2
            (L0 i (d0 (c0 i.succ))).1 (L0 i (d0 (c0 i.succ))).2 ell0 ell0,
          (∀ i, (B0 i).lowerArc = g0 '' Icc (c0 i.castSucc) (c0 i.succ) ∧
            (B0 i).leftCut = segment ℝ (g0 (c0 i.castSucc))
              (g0 (c0 i.castSucc) + ell0 • d0 (c0 i.castSucc)) ∧
            (B0 i).rightCut = segment ℝ (g0 (c0 i.succ))
              (g0 (c0 i.succ) + ell0 • d0 (c0 i.succ)) ∧
            (B0 i).carrier ⊆ closure U ∧ (B0 i).carrier \ (B0 i).lowerArc ⊆ U) ∧
          (∀ i j : Fin n0, i.succ < j.castSucc → Disjoint (B0 i).carrier (B0 j).carrier) ∧
          (∀ i j : Fin n0, i.succ = j.castSucc →
            (B0 i).carrier ∩ (B0 j).carrier = segment ℝ (g0 (c0 i.succ))
              (g0 (c0 i.succ) + ell0 • d0 (c0 i.succ))) ∧
          (∀ i, (D false ∪ D true) ∩ (B0 i).carrier =
            (if c0 i.castSucc = r0 false then (B0 i).leftCut else ∅) ∪
              (if c0 i.succ = A - r0 true then (B0 i).rightCut else ∅)) ∧
          (∀ p ∈ Icc (0 : ℝ) A, ∃ W : Set AnnulusCoordinates,
            IsOpen W ∧ g0 p ∈ W ∧
              W ∩ closure U ⊆ (D false ∪ D true) ∪ ⋃ i, (B0 i).carrier) ∧
    ∃ rev1 : Bool,
      let g1 : ℝ → AnnulusCoordinates := fun t => beta (if rev1 then B - t else t)
      let r1 (e : Bool) := r (if rev1 then !e else e)
      ∃ (d1 : ℝ → AnnulusCoordinates) (n1 : ℕ) (c1 : Fin (n1 + 1) → ℝ)
        (L1 : Fin n1 → AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
        (G1 : Fin n1 → OpenPartialHomeomorph ℝ ℝ) (f1 : Fin n1 → ℝ → ℝ) (ell1 : ℝ),
        0 < n1 ∧ StrictMono c1 ∧ c1 0 = r1 false ∧ c1 (Fin.last n1) = B - r1 true ∧ 0 < ell1 ∧
        ∃ B1 : ∀ i : Fin n1,
          ObliqueBandFaces
            (collarParameterEquiv.trans (L1 i).symm).toHomeomorph.toOpenPartialHomeomorph
            (f1 i) (G1 i (c1 i.castSucc)) (G1 i (c1 i.succ))
            (L1 i (d1 (c1 i.castSucc))).1 (L1 i (d1 (c1 i.castSucc))).2
            (L1 i (d1 (c1 i.succ))).1 (L1 i (d1 (c1 i.succ))).2 ell1 ell1,
          (∀ i, (B1 i).lowerArc = g1 '' Icc (c1 i.castSucc) (c1 i.succ) ∧
            (B1 i).leftCut = segment ℝ (g1 (c1 i.castSucc))
              (g1 (c1 i.castSucc) + ell1 • d1 (c1 i.castSucc)) ∧
            (B1 i).rightCut = segment ℝ (g1 (c1 i.succ))
              (g1 (c1 i.succ) + ell1 • d1 (c1 i.succ)) ∧
            (B1 i).carrier ⊆ closure U ∧ (B1 i).carrier \ (B1 i).lowerArc ⊆ U) ∧
          (∀ i j : Fin n1, i.succ < j.castSucc → Disjoint (B1 i).carrier (B1 j).carrier) ∧
          (∀ i j : Fin n1, i.succ = j.castSucc →
            (B1 i).carrier ∩ (B1 j).carrier = segment ℝ (g1 (c1 i.succ))
              (g1 (c1 i.succ) + ell1 • d1 (c1 i.succ))) ∧
          (∀ i, (D false ∪ D true) ∩ (B1 i).carrier =
            (if c1 i.castSucc = r1 false then (B1 i).leftCut else ∅) ∪
              (if c1 i.succ = B - r1 true then (B1 i).rightCut else ∅)) ∧
          (∀ p ∈ Icc (0 : ℝ) B, ∃ W : Set AnnulusCoordinates,
            IsOpen W ∧ g1 p ∈ W ∧
              W ∩ closure U ⊆ (D false ∪ D true) ∪ ⋃ i, (B1 i).carrier)
          ∧ ∀ i j, Disjoint (B0 i).carrier (B1 j).carrier := by
  classical
  obtain ⟨H, r, F, W, positive, hdata, hCC⟩ :=
    m64Intrinsic_exists_disjoint_two_corner_caps ha hb hA hB hai hbi hbase hend
      hind0 hind1 hU hV hdisj hfU hfV
  let D (e : Bool) := ⋃ i,
    ⋃ (_ : if positive e then i = (true, true) else i ≠ (true, true)),
      F e i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e}
  have hr (e : Bool) := (hdata e).1
  have hrbound (e : Bool) := (hdata e).2.1
  have hax0 (e : Bool) := (hdata e).2.2.2.2.2.2.1
  have hax1 (e : Bool) := (hdata e).2.2.2.2.2.2.2.1
  have hsmall (e : Bool) := (hdata e).2.2.2.2.2.2.2.2.1
  have hFdata (e : Bool) := (hdata e).2.2.2.2.2.2.2.2.2.2.2.1
  have hW (e : Bool) := (hdata e).2.2.2.2.2.2.2.2.2.2.2.2.1
  have hpW (e : Bool) := (hdata e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hsub (e : Bool) := (hdata e).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcover (e : Bool) := (hdata e).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcontact (e : Bool) := (hdata e).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hrA (e : Bool) : r e ≤ A / 3 :=
    (hrbound e).trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hrB (e : Bool) : r e ≤ B / 3 :=
    (hrbound e).trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num))
  have hnearA (e : Bool) :
      (fun s => alpha (if e then A - s else s)) '' Icc 0 (r e) ⊆ alpha '' Icc 0 A := by
    rintro z ⟨s, hs, rfl⟩
    refine ⟨if e then A - s else s, ?_, rfl⟩
    cases e
    · change s ∈ Icc (0 : ℝ) A
      exact ⟨hs.1, by linarith [hs.2, hrA false]⟩
    · change A - s ∈ Icc (0 : ℝ) A
      constructor <;> linarith [hs.1, hs.2, hrA true]
  have hnearB (e : Bool) :
      (fun s => beta (if e then B - s else s)) '' Icc 0 (r e) ⊆ beta '' Icc 0 B := by
    rintro z ⟨s, hs, rfl⟩
    refine ⟨if e then B - s else s, ?_, rfl⟩
    cases e
    · change s ∈ Icc (0 : ℝ) B
      exact ⟨hs.1, by linarith [hs.2, hrB false]⟩
    · change B - s ∈ Icc (0 : ℝ) B
      constructor <;> linarith [hs.1, hs.2, hrB true]
  have havoid0 := m64Intrinsic_two_arc_interior_disjoint hai hinter
  have hinter' : (beta '' Icc 0 B) ∩ (alpha '' Icc 0 A) ⊆ {beta 0, beta B} := by
    rw [hbase, hend, inter_comm]
    exact hinter
  have havoid1 := m64Intrinsic_two_arc_interior_disjoint hbi hinter'
  have hcompact0 : IsCompact (alpha '' Icc 0 A) := isCompact_Icc.image ha.continuous
  have hcompact1 : IsCompact (beta '' Icc 0 B) := isCompact_Icc.image hb.continuous
  have htip0 (e : Bool) : (r e, (0 : ℝ)) ∈ (H e).source := by
    simpa [sectorParameterEquiv_apply] using
      (hsmall e (true, true) (r e) ⟨(hr e).le, le_rfl⟩).1
  have htip1 (e : Bool) : ((0 : ℝ), r e) ∈ (H e).source := by
    simpa [sectorParameterEquiv_apply] using
      (hsmall e (true, true) (r e) ⟨(hr e).le, le_rfl⟩).2
  have hcontact0 (e : Bool) : D e ∩ frontier U ⊆
      (fun s => alpha (if e then A - s else s)) '' Icc 0 (r e) ∪ beta '' Icc 0 B := by
    rw [hcontact e]
    exact union_subset_union_right _ (hnearB e)
  have hcontact1 (e : Bool) : D e ∩ frontier U ⊆
      (fun s => beta (if e then B - s else s)) '' Icc 0 (r e) ∪ alpha '' Icc 0 A := by
    rw [hcontact e]
    exact union_subset (fun z hz => Or.inr (hnearA e hz)) (fun _ hz => Or.inl hz)
  have hcorner0 (e : Bool) : ∃ Q : Set AnnulusCoordinates, IsOpen Q ∧
      alpha (if e then A else 0) ∈ Q ∧ Q ∩ closure U ⊆ D e :=
    ⟨W e, hW e, hpW e, hcover e⟩
  have hcorner1 (e : Bool) : ∃ Q : Set AnnulusCoordinates, IsOpen Q ∧
      beta (if e then B else 0) ∈ Q ∧ Q ∩ closure U ⊆ D e := by
    refine ⟨W e, hW e, ?_, hcover e⟩
    cases e
    · simpa only [Bool.false_eq_true, if_false, hbase] using hpW false
    · simpa only [if_true, hend] using hpW true
  obtain ⟨rev0, d0, n0, c0, L0, G0, f0, ell0, hn0, hc0, hfirst0, hlast0, hell0,
    B0, _, hB0, hsep0, hadj0, hcap0, hcover0⟩ :=
    m64Intrinsic_exists_two_corner_oriented_arc_bands ha hai hareg hcompact1
      (fun t ht => disjoint_left.mp havoid0 ⟨t, ht, rfl⟩)
      hU hV hdisj hfU hfV r hr hrA H F positive (fun _ => false)
      (fun e i => (hFdata e i).1) (fun e i => (hFdata e i).2.2.1)
      (fun e i => (hFdata e i).2.2.2.1) (fun e i => (hFdata e i).2.2.2.2.1)
      (fun e i => (hFdata e i).2.2.2.2.2.1)
      (fun e i => (hFdata e i).2.2.2.2.2.2.1)
      (fun e i => (hFdata e i).2.2.2.2.2.2.2.1)
      hax0 htip0 isOpen_univ (subset_univ _) hsub hCC hcontact0 hcorner0
  let g0 : ℝ → AnnulusCoordinates := fun t => alpha (if rev0 then A - t else t)
  let r0 (e : Bool) := r (if rev0 then !e else e)
  have hr0 (e : Bool) : 0 < r0 e := hr _
  have hcut0 (k : Fin (n0 + 1)) : c0 k ∈ Icc (r0 false) (A - r0 true) :=
    ⟨by simpa only [hfirst0] using hc0.monotone (Fin.zero_le k),
      by simpa only [hlast0] using hc0.monotone (Fin.le_last k)⟩
  have hlower0 (i : Fin n0) : (B0 i).lowerArc ⊆ alpha '' Ioo 0 A := by
    rw [(hB0 i).1]
    rintro z ⟨t, ht, rfl⟩
    have ht0 : 0 < t := (hr0 false).trans_le ((hcut0 i.castSucc).1.trans ht.1)
    have htA : t < A := (ht.2.trans (hcut0 i.succ).2).trans_lt (sub_lt_self A (hr0 true))
    refine ⟨if rev0 then A - t else t, ?_, rfl⟩
    cases rev0
    · exact ⟨ht0, htA⟩
    · change A - t ∈ Ioo (0 : ℝ) A
      constructor <;> linarith
  let O := (⋃ i, (B0 i).carrier)ᶜ
  obtain ⟨hO, hOarc⟩ := m64Intrinsic_arc_band_carriers_avoid_remainder
    (fun i => (B0 i).carrier) (fun i => (B0 i).lowerArc)
      (fun i => (B0 i).isClosed_carrier) hU hfU havoid0 hlower0
      (fun i => (hB0 i).2.2.2.2)
  have hfU' : frontier U = beta '' Icc 0 B ∪ alpha '' Icc 0 A := hfU.trans (union_comm _ _)
  obtain ⟨rev1, d1, n1, c1, L1, G1, f1, ell1, hn1, hc1, hfirst1, hlast1, hell1,
    B1, hO1, hB1, hsep1, hadj1, hcap1, hcover1⟩ :=
    m64Intrinsic_exists_two_corner_oriented_arc_bands hb hbi hbreg hcompact0
      (fun t ht => disjoint_left.mp havoid1 ⟨t, ht, rfl⟩)
      hU hV hdisj hfU' hfV r hr hrB H F positive (fun _ => true)
      (fun e i => (hFdata e i).1) (fun e i => (hFdata e i).2.2.1)
      (fun e i => (hFdata e i).2.2.2.1) (fun e i => (hFdata e i).2.2.2.2.1)
      (fun e i => (hFdata e i).2.2.2.2.2.1)
      (fun e i => (hFdata e i).2.2.2.2.2.2.1)
      (fun e i => (hFdata e i).2.2.2.2.2.2.2.1)
      hax1 htip1 hO hOarc hsub hCC hcontact1 hcorner1
  refine ⟨H, r, F, W, positive, hdata, hCC,
    rev0, d0, n0, c0, L0, G0, f0, ell0, hn0, hc0, hfirst0, hlast0, hell0,
    B0, hB0, hsep0, hadj0, hcap0, hcover0,
    rev1, d1, n1, c1, L1, G1, f1, ell1, hn1, hc1, hfirst1, hlast1, hell1,
    B1, hB1, hsep1, hadj1, hcap1, hcover1, ?_⟩
  intro i j
  exact disjoint_left.mpr (fun p hp0 hp1 => hO1 j hp1 (mem_iUnion.mpr ⟨i, hp0⟩))

end PoincareConjecture
