import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ThreeArcCapAvoidance
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_PairedCapPatchChains

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves PoincareConjecture.Topology.Surface
open ChartCircleArrangementVertexPatch

namespace PoincareConjecture

theorem m64Intrinsic_exists_three_arc_paired_chains
    (gamma : Bool → ℝ → AnnulusCoordinates) (sigma : ℝ → AnnulusCoordinates)
    (T r b : Bool → ℝ) {S delta : ℝ}
    (hg : ∀ e, ContDiff ℝ ∞ (gamma e)) (hs : Continuous sigma)
    (hT : ∀ e, 0 < T e) (hS : 0 < S) (hdelta : 0 < delta)
    (hr : ∀ e, 0 < r e) (hrbound : ∀ e, r e ≤ min (T e) S / 3)
    (hb : ∀ e, b e ∈ Ioo (0 : ℝ) (T e))
    (hgap : ∀ e : Bool, (if e then b e else r e) < if e then T e - r e else b e)
    (hinj : ∀ e, InjOn (gamma e) (Icc 0 (T e)))
    (hregular : ∀ e, ∀ t ∈ Ioo (0 : ℝ) (T e), deriv (gamma e) t ≠ 0)
    (hjoin : gamma false (T false) = gamma true 0)
    (hab : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 (T true),
      gamma false x = gamma true y → x = T false ∧ y = 0)
    (has : ∀ x ∈ Icc 0 (T false), ∀ y ∈ Icc 0 S,
      gamma false x = sigma y → x = 0 ∧ y = 0)
    (hbs : ∀ x ∈ Icc 0 (T true), ∀ y ∈ Icc 0 S,
      gamma true x = sigma y → x = T true ∧ y = S)
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V)
    (hfront : frontier U = gamma false '' Icc 0 (T false) ∪
      gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S)
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
    (hopen : ∀ e, (P e).carrier \ (P e).lowerArc ⊆ U) :
    let C (e : Bool) := ⋃ i,
      ⋃ (_ : if positive e then i = (true, true) else i ≠ (true, true)),
        F e i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e}
    (∀ e, C e ⊆ closure U) →
    (∀ e, (P e).carrier ⊆ (C false ∪ C true ∪ sigma '' Icc 0 S)ᶜ) →
    (∀ e : Bool, C e ∩ frontier U ⊆
      (fun s => gamma e (if e then T e - s else s)) '' Icc 0 (r e) ∪
        (fun s => sigma (if e then S - s else s)) '' Icc 0 (r e)) →
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
      sigma '' Icc 0 S ⊆
        ((⋃ i, ((E false).band i).carrier) ∪ (⋃ i, ((E true).band i).carrier))ᶜ := by
  classical
  intro C hCsub hPavoid hCfront hcorner
  have hrT (e : Bool) : r e < T e := by
    have := (hrbound e).trans
      (div_le_div_of_nonneg_right (min_le_left (T e) S) (by norm_num : (0 : ℝ) ≤ 3))
    linarith [hT e]
  have hrS (e : Bool) : r e < S := by
    have := (hrbound e).trans
      (div_le_div_of_nonneg_right (min_le_right (T e) S) (by norm_num : (0 : ℝ) ≤ 3))
    linarith
  have hCC (e : Bool) : IsCompact (C e) := by
    apply isCompact_iUnion
    intro i
    apply isCompact_iUnion
    intro _
    exact m64Intrinsic_cap_isCompact (F e i) (hcap e i).1
  have hcontact0 : C false ∩ frontier U ⊆
      gamma false '' Icc 0 (r false) ∪ sigma '' Icc 0 (r false) := hCfront false
  have hcontact1 : C true ∩ frontier U ⊆
      (fun s => gamma true (T true - s)) '' Icc 0 (r true) ∪
      (fun s => sigma (S - s)) '' Icc 0 (r true) := hCfront true
  obtain ⟨hsep0, hsep1, _, _⟩ := m64Intrinsic_three_arc_cap_avoidance hs
    (hT false) (hT true) hS (hrbound false) (hrbound true) hjoin hab has hbs
    hfront (hCC false) (hCC true) hcontact0 hcontact1
  have hCother (e : Bool) : Disjoint (C e) (gamma (!e) '' Icc 0 (T (!e))) := by
    cases e
    · exact hsep0
    · exact hsep1
  have hCunion (e : Bool) : C e ⊆ C false ∪ C true := by
    cases e
    · exact subset_union_left
    · exact subset_union_right
  have hCP (e : Bool) : Disjoint (C e) ((P false).carrier ∪ (P true).carrier) := by
    apply disjoint_left.mpr
    rintro p hpC (hp | hp)
    · exact hPavoid false hp (Or.inl (hCunion e hpC))
    · exact hPavoid true hp (Or.inl (hCunion e hpC))
  have hfront' (e : Bool) : frontier U = gamma e '' Icc 0 (T e) ∪
      (gamma (!e) '' Icc 0 (T (!e)) ∪ sigma '' Icc 0 S) := by
    cases e
    · change frontier U = gamma false '' Icc 0 (T false) ∪
        (gamma true '' Icc 0 (T true) ∪ sigma '' Icc 0 S)
      exact hfront.trans (union_assoc _ _ _)
    · change frontier U = gamma true '' Icc 0 (T true) ∪
        (gamma false '' Icc 0 (T false) ∪ sigma '' Icc 0 S)
      rw [hfront]
      ac_rfl
  have havoid (e : Bool) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) (T e)) :
      gamma e t ∉ gamma (!e) '' Icc 0 (T (!e)) ∪ sigma '' Icc 0 S := by
    cases e
    · rintro (⟨y, hy, he⟩ | ⟨y, hy, he⟩)
      · exact ht.2.ne (hab t (Ioo_subset_Icc_self ht) y hy he.symm).1
      · exact ht.1.ne' (has t (Ioo_subset_Icc_self ht) y hy he.symm).1
    · rintro (⟨x, hx, he⟩ | ⟨y, hy, he⟩)
      · exact ht.1.ne' (hab x hx t (Ioo_subset_Icc_self ht) he).2
      · exact ht.2.ne (hbs t (Ioo_subset_Icc_self ht) y hy he.symm).1
  have hnear (e : Bool) :
      (fun s => sigma (if e then S - s else s)) '' Icc 0 (r e) ⊆ sigma '' Icc 0 S := by
    rintro p ⟨s, hs, rfl⟩
    refine ⟨if e then S - s else s, ?_, rfl⟩
    cases e
    · exact ⟨hs.1, hs.2.trans (hrS false).le⟩
    · change S - s ∈ Icc (0 : ℝ) S
      constructor <;> linarith [hs.1, hs.2, hrS true]
  have hcontact (e : Bool) : C e ∩ frontier U ⊆
      (fun s => gamma e (if e then T e - s else s)) '' Icc 0 (r e) ∪
        (gamma (!e) '' Icc 0 (T (!e)) ∪ sigma '' Icc 0 S) := by
    intro p hp
    rcases hCfront e hp with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (hnear e h))
  exact m64Intrinsic_exists_paired_cap_patch_chains gamma T r b hg hr hrT hb hgap hinj
    hregular (isCompact_Icc.image hs) havoid hU hV hUV hfront' hfV hray
    H F positive hcap haxis htip L f a0 a1 ua wa ub wb ra rb ha01 P
    hbase htangent htrans hlower hopen hdelta hCsub hCP hCother hcontact hcorner

end PoincareConjecture
