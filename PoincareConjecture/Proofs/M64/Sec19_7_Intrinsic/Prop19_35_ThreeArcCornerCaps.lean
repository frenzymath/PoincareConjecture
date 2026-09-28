import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FiniteCornerCaps





noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Matrix
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture





theorem m64Intrinsic_exists_three_arc_corner_caps
    {alpha beta sigma : ℝ → AnnulusCoordinates}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta) (hs : ContDiff ℝ ∞ sigma)
    {A B T : ℝ} (hA : 0 < A) (hB : 0 < B) (hT : 0 < T)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hsi : InjOn sigma (Icc 0 T))
    (hstart : sigma 0 = alpha 0) (hend : sigma T = beta B)
    (hab : ∀ x ∈ Icc 0 A, ∀ y ∈ Icc 0 B,
      alpha x = beta y → x = A ∧ y = 0)
    (hind0 : LinearIndependent ℝ
      (![deriv alpha 0, deriv sigma 0] : Fin 2 → AnnulusCoordinates))
    (hind1 : LinearIndependent ℝ
      (![-deriv beta B, -deriv sigma T] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V)
    (hfront : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B ∪ sigma '' Icc 0 T)
    (hfV : frontier V = frontier U) :
    ∃ (H : Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) (r : Bool → ℝ)
      (F : Bool → Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
      (W : Bool → Set AnnulusCoordinates) (positive : Bool → Bool),
      let C (e : Bool) (i : Bool × Bool) :=
        F e i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r e}
      let D (e : Bool) := ⋃ i,
        ⋃ (_ : if positive e then i = (true, true) else i ≠ (true, true)), C e i
      (∀ e : Bool,
        0 < r e ∧ r e ≤ min (if e then B else A) T / 3 ∧
        (0 : ℝ × ℝ) ∈ (H e).source ∧ H e 0 = (if e then beta B else alpha 0) ∧
        ContDiffOn ℝ ∞ (H e) (H e).source ∧ ContDiffOn ℝ ∞ (H e).symm (H e).target ∧
        (∀ s : ℝ, H e (s, 0) = if e then beta (B - s) else alpha s) ∧
        (∀ s : ℝ, H e (0, s) = sigma (if e then T - s else s)) ∧
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
        IsOpen (W e) ∧ (if e then beta B else alpha 0) ∈ W e ∧
        IsCompact (D e) ∧ D e ⊆ closure U ∧ W e ∩ closure U ⊆ D e ∧
        D e ∩ frontier U =
          (fun s => if e then beta (B - s) else alpha s) '' Icc 0 (r e) ∪
          (fun s => sigma (if e then T - s else s)) '' Icc 0 (r e)) ∧
      Disjoint (D false) (D true) := by
  classical
  let left : Bool → ℝ → AnnulusCoordinates := fun e s =>
    if e then beta (B - s) else alpha s
  let right : Bool → ℝ → AnnulusCoordinates := fun e s => sigma (if e then T - s else s)
  let len : Bool → ℝ := fun e => if e then B else A
  let K : Bool → Set AnnulusCoordinates := fun e =>
    if e then alpha '' Icc 0 A else beta '' Icc 0 B
  have hleft (e : Bool) : ContDiff ℝ ∞ (left e) := by
    cases e
    · exact ha
    · exact hb.comp (contDiff_const.sub contDiff_id)
  have hright (e : Bool) : ContDiff ℝ ∞ (right e) := by
    cases e
    · exact hs
    · exact hs.comp (contDiff_const.sub contDiff_id)
  have hlen (e : Bool) : 0 < len e := by cases e <;> assumption
  have hli (e : Bool) : InjOn (left e) (Icc 0 (len e)) := by
    cases e
    · exact hai
    · intro s hs t ht heq
      change s ∈ Icc (0 : ℝ) B at hs
      change t ∈ Icc (0 : ℝ) B at ht
      change beta (B - s) = beta (B - t) at heq
      have he := hbi ⟨by linarith [hs.2], by linarith [hs.1]⟩
        ⟨by linarith [ht.2], by linarith [ht.1]⟩ heq
      linarith
  have hri (e : Bool) : InjOn (right e) (Icc 0 T) := by
    cases e
    · exact hsi
    · intro s hs t ht heq
      change sigma (T - s) = sigma (T - t) at heq
      have he := hsi ⟨by linarith [hs.2], by linarith [hs.1]⟩
        ⟨by linarith [ht.2], by linarith [ht.1]⟩ heq
      linarith
  have hbase (e : Bool) : right e 0 = left e 0 := by
    cases e
    · exact hstart
    · simpa only [left, right, if_true, sub_zero] using hend
  have hind (e : Bool) : LinearIndependent ℝ
      (![deriv (left e) 0, deriv (right e) 0] : Fin 2 → AnnulusCoordinates) := by
    cases e
    · exact hind0
    · simpa only [left, right, if_true, deriv_comp_const_sub, sub_zero] using hind1
  have hK (e : Bool) : IsCompact (K e) := by
    cases e
    · exact isCompact_Icc.image hb.continuous
    · exact isCompact_Icc.image ha.continuous
  have hpK (e : Bool) : left e 0 ∉ K e := by
    cases e
    · rintro ⟨t, ht, he⟩
      exact hA.ne' (hab 0 ⟨le_rfl, hA.le⟩ t ht he.symm).1.symm
    · rintro ⟨t, ht, he⟩
      have he' : alpha t = beta B := by simpa only [left, if_true, sub_zero] using he
      exact hB.ne' (hab t ht B ⟨hB.le, le_rfl⟩ he').2
  have hneq : alpha 0 ≠ beta B := by
    intro he
    exact hA.ne' (hab 0 ⟨le_rfl, hA.le⟩ B ⟨hB.le, le_rfl⟩ he).1.symm
  have hdistinct : Function.Injective (fun e => left e 0) := by
    intro e f he
    cases e <;> cases f
    · rfl
    · exact (hneq (by simpa only [left, Bool.false_eq_true, if_false, if_true, sub_zero]
        using he)).elim
    · exact (hneq (by simpa only [left, Bool.false_eq_true, if_false, if_true, sub_zero]
        using he.symm)).elim
    · rfl
  have hleftImage (e : Bool) : left e '' Icc 0 (len e) =
      if e then beta '' Icc 0 B else alpha '' Icc 0 A := by
    cases e
    · rfl
    · change (beta ∘ fun s => B - s) '' Icc 0 B = _
      rw [image_comp, image_const_sub_Icc]
      simp only [sub_self, sub_zero, if_true]
  have hrightImage (e : Bool) : right e '' Icc 0 T = sigma '' Icc 0 T := by
    cases e
    · rfl
    · change (sigma ∘ fun s => T - s) '' Icc 0 T = _
      rw [image_comp, image_const_sub_Icc]
      simp only [sub_self, sub_zero]
  have hf (e : Bool) : frontier U = left e '' Icc 0 (len e) ∪ right e '' Icc 0 T ∪ K e := by
    rw [hleftImage, hrightImage, hfront]
    cases e <;> simp only [K, Bool.false_eq_true, if_false, if_true] <;> ac_rfl
  obtain ⟨H, r, F, W, positive, hdata, hsep⟩ :=
    m64Intrinsic_exists_disjoint_finite_corner_caps left right len (fun _ => T) K
      hleft hright hlen (fun _ => hT) hli hri hbase hind hK hpK hdistinct hU hV hUV hf hfV
  refine ⟨H, r, F, W, positive, ?_, hsep Bool.false_ne_true⟩
  intro e
  simpa only [left, right, len, sub_zero] using hdata e

end PoincareConjecture
