import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcCapSeparators

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Matrix
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture

theorem m64Intrinsic_exists_disjoint_two_corner_caps
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
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
      Disjoint (D false) (D true) := by
  classical
  have hneq : alpha 0 ≠ alpha A := by
    intro heq
    exact hA.ne' (hai ⟨le_rfl, hA.le⟩ ⟨hA.le, le_rfl⟩ heq).symm
  obtain ⟨O0, O1, hO0, hO1, hp0, hp1, hOO⟩ := t2_separation hneq
  let O : Bool → Set AnnulusCoordinates := fun e => if e then O1 else O0
  let a : Bool → ℝ → AnnulusCoordinates := fun e s => alpha (if e then A - s else s)
  let b : Bool → ℝ → AnnulusCoordinates := fun e s => beta (if e then B - s else s)
  have ha' (e : Bool) : ContDiff ℝ ∞ (a e) := by
    cases e
    · exact ha
    · exact ha.comp (contDiff_const.sub contDiff_id)
  have hb' (e : Bool) : ContDiff ℝ ∞ (b e) := by
    cases e
    · exact hb
    · exact hb.comp (contDiff_const.sub contDiff_id)
  have hai' (e : Bool) : InjOn (a e) (Icc 0 A) := by
    cases e
    · exact hai
    · intro s hs t ht heq
      change alpha (A - s) = alpha (A - t) at heq
      have he := hai ⟨by linarith [hs.2], by linarith [hs.1]⟩
        ⟨by linarith [ht.2], by linarith [ht.1]⟩ heq
      linarith
  have hbi' (e : Bool) : InjOn (b e) (Icc 0 B) := by
    cases e
    · exact hbi
    · intro s hs t ht heq
      change beta (B - s) = beta (B - t) at heq
      have he := hbi ⟨by linarith [hs.2], by linarith [hs.1]⟩
        ⟨by linarith [ht.2], by linarith [ht.1]⟩ heq
      linarith
  have hbase' (e : Bool) : b e 0 = a e 0 := by
    cases e
    · exact hbase
    · simpa only [a, b, if_true, sub_zero] using hend
  have hind' (e : Bool) : LinearIndependent ℝ
      (![deriv (a e) 0, deriv (b e) 0] : Fin 2 → AnnulusCoordinates) := by
    cases e
    · exact hind0
    · simpa only [a, b, if_true, deriv_comp_const_sub, sub_zero] using hind1
  have haimage (e : Bool) : a e '' Icc 0 A = alpha '' Icc 0 A := by
    cases e
    · rfl
    · change (alpha ∘ fun s => A - s) '' Icc 0 A = _
      rw [image_comp, image_const_sub_Icc]
      simp only [sub_self, sub_zero]
  have hbimage (e : Bool) : b e '' Icc 0 B = beta '' Icc 0 B := by
    cases e
    · rfl
    · change (beta ∘ fun s => B - s) '' Icc 0 B = _
      rw [image_comp, image_const_sub_Icc]
      simp only [sub_self, sub_zero]
  have hfront (e : Bool) : frontier U = a e '' Icc 0 A ∪ b e '' Icc 0 B ∪ ∅ := by
    rw [haimage, hbimage, union_empty]
    exact hfU
  have hopen (e : Bool) : IsOpen (O e) := by cases e <;> assumption
  have hpoint (e : Bool) : a e 0 ∈ O e := by
    cases e
    · exact hp0
    · simpa only [a, O, if_true, sub_zero] using hp1
  have hcorner (e : Bool) := m64Intrinsic_exists_two_arc_corner_caps
    (ha' e) (hb' e) hA hB (hai' e) (hbi' e) (hbase' e) (hind' e)
    isCompact_empty (notMem_empty _) hU hV hdisj (hfront e) hfV (hopen e) (hpoint e)
  choose H r F W positive hdata using hcorner
  let C (e : Bool) (i : Bool × Bool) :=
    F e i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e}
  let D (e : Bool) := ⋃ i, ⋃ (_ : if positive e then i = (true, true) else i ≠ (true, true)), C e i
  have hDO (e : Bool) : D e ⊆ O e := (hdata e).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨H, r, F, W, positive, ?_, hOO.mono (hDO false) (hDO true)⟩
  intro e
  obtain ⟨hr, hrbound, hzero, hbaseH, _, hH, hHi, haxis, haxis', hsmall,
    hfrontier, hside, hF, hW, hpW, _, hsub, hcover, hcontact⟩ := hdata e
  have hcompact : IsCompact (D e) := by
    apply isCompact_iUnion
    intro i
    apply isCompact_iUnion
    intro _
    exact m64Intrinsic_cap_isCompact (F e i) (hF i).1
  have hbaseeq : a e 0 = alpha (if e then A else 0) := by cases e <;> simp [a]
  exact ⟨hr, hrbound, hzero, hbaseH.trans hbaseeq, hH, hHi, haxis, haxis',
    hsmall, hfrontier, hside, hF, hW, hbaseeq ▸ hpW, hcompact, hsub, hcover, hcontact⟩

end PoincareConjecture
