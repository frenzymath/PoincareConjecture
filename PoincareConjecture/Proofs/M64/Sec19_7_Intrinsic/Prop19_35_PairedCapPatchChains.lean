import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_SmallCapPatchChain
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ArcBandOppositeNeighborhood





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture






theorem m64Intrinsic_exists_paired_cap_patch_chains
    (gamma : Bool → ℝ → AnnulusCoordinates) (T r b : Bool → ℝ)
    (hg : ∀ e, ContDiff ℝ ∞ (gamma e)) (hr : ∀ e, 0 < r e) (hrT : ∀ e, r e < T e)
    (hb : ∀ e, b e ∈ Ioo (0 : ℝ) (T e))
    (hgap : ∀ e : Bool, (if e then b e else r e) < if e then T e - r e else b e)
    (hinj : ∀ e, InjOn (gamma e) (Icc 0 (T e)))
    (hregular : ∀ e, ∀ t ∈ Ioo (0 : ℝ) (T e), deriv (gamma e) t ≠ 0)
    {K U V : Set AnnulusCoordinates} (hK : IsCompact K)
    (havoid : ∀ e, ∀ t ∈ Ioo (0 : ℝ) (T e),
      gamma e t ∉ gamma (!e) '' Icc 0 (T (!e)) ∪ K)
    (hU : IsOpen U) (hV : IsOpen V) (hUV : Disjoint U V)
    (hfront : ∀ e, frontier U = gamma e '' Icc 0 (T e) ∪
      (gamma (!e) '' Icc 0 (T (!e)) ∪ K))
    (hfV : frontier V = frontier U)
    (hray : ∀ e, ∀ t ∈ Ioo (0 : ℝ) (T e), ∀ᶠ z in 𝓝[>] (0 : ℝ),
      gamma e t + z • quarterTurn (deriv (gamma e) t) ∈ U)
    (H : Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (F : Bool → Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (positive : Bool → Bool)
    (hcap : ∀ e i,
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e} ⊆ (F e i).source ∧
      ContDiffOn ℝ ∞ (F e i) (F e i).source ∧
      ContDiffOn ℝ ∞ (F e i).symm (F e i).target ∧
      (∀ s ∈ Icc (0 : ℝ) (r e), F e i (s, 0) = H e (sectorParameterEquiv 0 i (s, 0))) ∧
      (∀ s ∈ Icc (0 : ℝ) (r e), F e i (0, s) = H e (sectorParameterEquiv 0 i (0, s))) ∧
      (∀ t : ℝ, F e i ((1 - t) * r e, t * r e) =
        (1 - t) • F e i (r e, 0) + t • F e i (0, r e)) ∧
      F e i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e} ⊆
        H e '' ((H e).source ∩ (sectorParameterEquiv 0 i) ''
          {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (haxis : ∀ (e : Bool) (s : ℝ), H e (s, 0) = gamma e (if e then T e - s else s))
    (htip : ∀ e, (r e, (0 : ℝ)) ∈ (H e).source)
    (L : Bool → (ℝ × ℝ) ≃L[ℝ] AnnulusCoordinates) (f : Bool → ℝ → ℝ)
    (a0 a1 ua wa ub wb ra rb : Bool → ℝ) (ha01 : ∀ e, a0 e < a1 e)
    (P : ∀ e, ObliqueBandFaces
      (collarParameterEquiv.trans (L e)).toHomeomorph.toOpenPartialHomeomorph
      (f e) (a0 e) (a1 e) (ua e) (wa e) (ub e) (wb e) (ra e) (rb e))
    (hbase : ∀ e : Bool,
      L e (if e then a1 e else a0 e, f e (if e then a1 e else a0 e)) = gamma e (b e))
    (htangent : ∀ e : Bool, ∃ speed : ℝ, 0 < speed ∧
      deriv (gamma e) (b e) = speed • L e (1, deriv (f e) (if e then a1 e else a0 e)))
    (htrans : ∀ e : Bool, 0 < inner ℝ (quarterTurn (deriv (gamma e) (b e)))
      (if e then L e (ub e, wb e) else L e (ua e, wa e)))
    (hlower : ∀ e : Bool,
      (P e).lowerArc = if e then gamma e '' Icc 0 (b e) else gamma e '' Icc (b e) (T e))
    (hopen : ∀ e, (P e).carrier \ (P e).lowerArc ⊆ U)
    {delta : ℝ} (hdelta : 0 < delta) :
    let C (e : Bool) := ⋃ i,
      ⋃ (_ : if positive e then i = (true, true) else i ≠ (true, true)),
        F e i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e}
    (∀ e, C e ⊆ closure U) →
    (∀ e, Disjoint (C e) ((P false).carrier ∪ (P true).carrier)) →
    (∀ e, Disjoint (C e) (gamma (!e) '' Icc 0 (T (!e)))) →
    (∀ e : Bool, C e ∩ frontier U ⊆
      (fun s => gamma e (if e then T e - s else s)) '' Icc 0 (r e) ∪
        (gamma (!e) '' Icc 0 (T (!e)) ∪ K)) →
    (∀ e : Bool, ∃ W : Set AnnulusCoordinates, IsOpen W ∧
      gamma e (if e then T e else 0) ∈ W ∧ W ∩ closure U ⊆ C e) →
    ∃ E : ∀ e : Bool, M64IntrinsicArcBandChain (gamma e)
        (if e then b e else r e) (if e then T e - r e else b e) U,
      (∀ e : Bool,
        (E e).length ≤ 1 ∧ (E e).length * (if e then rb e else ra e) < delta ∧
        (E e).direction (if e then T e - r e else r e) =
          F e (true, positive e) (0, r e) - F e (true, positive e) (r e, 0) ∧
        (E e).direction (b e) = (if e then rb e else ra e) •
          (if e then L e (ub e, wb e) else L e (ua e, wa e)) ∧
        (∀ z ∈ Icc (0 : ℝ) 1, gamma e (if e then T e - r e else r e) +
          z • (E e).direction (if e then T e - r e else r e) ∈ C e) ∧
        (∀ z ∈ Icc (0 : ℝ) 1, gamma e (b e) + z • (E e).direction (b e) ∈
          (P e).carrier ∪ (P (!e)).carrier) ∧
        (∀ i, ((E e).band i).carrier ⊆ (C (!e))ᶜ) ∧
        (∀ i, (C e ∪ ((P e).carrier ∪ (P (!e)).carrier)) ∩ ((E e).band i).carrier =
          (if (E e).cut i.castSucc = (if e then b e else r e)
            then ((E e).band i).leftCut else ∅) ∪
          (if (E e).cut i.succ = (if e then T e - r e else b e)
            then ((E e).band i).rightCut else ∅)) ∧
        ∀ p ∈ (if e then Ioc (b e) (T e) else Ico 0 (b e)),
          ∃ W : Set AnnulusCoordinates, IsOpen W ∧ gamma e p ∈ W ∧
            W ∩ closure U ⊆ C e ∪ ⋃ i, ((E e).band i).carrier) ∧
      (∀ i j, Disjoint ((E false).band i).carrier ((E true).band j).carrier) ∧
      IsOpen ((⋃ i, ((E false).band i).carrier) ∪ (⋃ i, ((E true).band i).carrier))ᶜ ∧
      K ⊆ ((⋃ i, ((E false).band i).carrier) ∪ (⋃ i, ((E true).band i).carrier))ᶜ := by
  classical
  intro C hCsub hCP hCother hCfront hcorner
  have hCclosed (e : Bool) : IsClosed (C e) := by
    apply IsCompact.isClosed
    apply isCompact_iUnion
    intro i
    apply isCompact_iUnion
    intro _
    exact m64Intrinsic_cap_isCompact (F e i) (hcap e i).1
  have hPfull (e : Bool) : (P e).lowerArc ⊆ gamma e '' Icc 0 (T e) := by
    rw [hlower]
    cases e
    · exact image_mono (Icc_subset_Icc (hb false).1.le le_rfl)
    · exact image_mono (Icc_subset_Icc le_rfl (hb true).2.le)
  have hZfront (e : Bool) : (P (!e)).carrier ∩ frontier U ⊆
      gamma (!e) '' Icc 0 (T (!e)) ∪ K := by
    rintro p ⟨hp, hpf⟩
    by_cases hl : p ∈ (P (!e)).lowerArc
    · exact Or.inl (hPfull (!e) hl)
    · exact ((disjoint_frontier_iff_isOpen.mpr hU).le_bot
        ⟨hpf, hopen (!e) ⟨hp, hl⟩⟩).elim
  have hwhole (e : Bool) : (P e).carrier ∪ (P (!e)).carrier =
      (P false).carrier ∪ (P true).carrier := by
    cases e
    · rfl
    · exact union_comm _ _
  have hclosedRemainder (e : Bool) :
      IsCompact (gamma (!e) '' Icc 0 (T (!e)) ∪ K) :=
    (isCompact_Icc.image (hg (!e)).continuous).union hK
  have hdisjRemainder (e : Bool) : Disjoint (gamma e '' Ioo 0 (T e))
      (gamma (!e) '' Icc 0 (T (!e)) ∪ K) := by
    apply disjoint_left.mpr
    rintro _ ⟨t, ht, rfl⟩ hp
    exact havoid e t ht hp
  have htrim (e : Bool) : Icc (if e then b e else r e) (if e then T e - r e else b e) ⊆
      Ioo (0 : ℝ) (T e) := by
    intro t ht
    cases e
    · exact ⟨(hr false).trans_le ht.1, ht.2.trans_lt (hb false).2⟩
    · exact ⟨(hb true).1.trans_le ht.1, ht.2.trans_lt (sub_lt_self _ (hr true))⟩
  have hbuild (e : Bool) (O : Set AnnulusCoordinates) (hO : IsOpen O)
      (haxisO : gamma e '' Icc (if e then b e else r e)
        (if e then T e - r e else b e) ⊆ O) :=
    m64Intrinsic_exists_small_cap_patch_chain (hg e) (hr e) (hrT e) (hb e) hdelta e
      (hgap e) (hinj e) (hregular e) (hclosedRemainder e) (havoid e)
      hU hV hUV (hfront e) hfV (hray e) (H e) (F e) (positive e) false
      (fun i => (hcap e i).1) (fun i => (hcap e i).2.1) (fun i => (hcap e i).2.2.1)
      (fun i => (hcap e i).2.2.2.1) (fun i => (hcap e i).2.2.2.2.1)
      (fun i => (hcap e i).2.2.2.2.2.1) (fun i => (hcap e i).2.2.2.2.2.2)
      (haxis e) (htip e) (L e) (ha01 e) (P e) (hbase e) (htangent e) (htrans e)
      (hlower e) (hopen e) (P (!e)).isClosed_carrier (hZfront e) hO haxisO
      (hCsub e) (by rw [hwhole]; exact hCP e) (hCfront e) (hcorner e)
  obtain ⟨E0, hE0⟩ := hbuild false (C true)ᶜ (hCclosed true).isOpen_compl (by
    intro p hp
    exact fun hpC => disjoint_left.mp (hCother true) hpC
      (image_mono (fun _ ht => Ioo_subset_Icc_self (htrim false ht)) hp))
  have havoidChains (e : Bool)
      (E : M64IntrinsicArcBandChain (gamma e)
        (if e then b e else r e) (if e then T e - r e else b e) U) :
      IsOpen (⋃ i, (E.band i).carrier)ᶜ ∧
        gamma (!e) '' Icc 0 (T (!e)) ∪ K ⊆ (⋃ i, (E.band i).carrier)ᶜ :=
    m64Intrinsic_arc_band_carriers_avoid_remainder
      (fun i => (E.band i).carrier) (fun i => (E.band i).lowerArc)
      (fun i => (E.band i).isClosed_carrier) hU (hfront e) (hdisjRemainder e)
      (fun i => (E.lower_subset i).trans (image_mono (htrim e))) E.off_lower
  have havoid0 := havoidChains false E0
  let O1 := (C false ∪ ⋃ i, (E0.band i).carrier)ᶜ
  have hO1 : IsOpen O1 :=
    ((hCclosed false).union
      (isClosed_iUnion_of_finite (fun i => (E0.band i).isClosed_carrier))).isOpen_compl
  obtain ⟨E1, hE1⟩ := hbuild true O1 hO1 (by
    intro p hp
    have hpfull := image_mono (fun _ ht => Ioo_subset_Icc_self (htrim true ht)) hp
    rintro (hpC | hpE)
    · exact disjoint_left.mp (hCother false) hpC hpfull
    · exact havoid0.2 (Or.inl hpfull) hpE)
  let E (e : Bool) : M64IntrinsicArcBandChain (gamma e)
      (if e then b e else r e) (if e then T e - r e else b e) U :=
    Bool.rec E0 E1 e
  have havoid1 := havoidChains true E1
  have hE1O := hE1.2.2.2.2.2.2.1
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · intro e
    cases e
    · exact hE0
    · refine ⟨hE1.1, hE1.2.1, hE1.2.2.1, hE1.2.2.2.1,
        hE1.2.2.2.2.1, hE1.2.2.2.2.2.1, ?_, hE1.2.2.2.2.2.2.2⟩
      intro i p hp hpC
      exact hE1O i hp (Or.inl hpC)
  · intro i j
    exact disjoint_left.mpr (fun p h0 h1 => hE1O j h1 (Or.inr (mem_iUnion.mpr ⟨i, h0⟩)))
  · exact ((isClosed_iUnion_of_finite (fun i => (E0.band i).isClosed_carrier)).union
      (isClosed_iUnion_of_finite (fun i => (E1.band i).isClosed_carrier))).isOpen_compl
  · intro p hp
    rintro (h0 | h1)
    · exact havoid0.2 (Or.inr hp) h0
    · exact havoid1.2 (Or.inr hp) h1

end PoincareConjecture
