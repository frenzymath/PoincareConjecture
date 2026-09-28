import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

set_option autoImplicit false

open Set Function

namespace PoincareConjecture.M25.Topology3D

theorem exists_circle_interval_complement
    (f : unitInterval → Circle)
    (hf : Continuous f) (hfi : Function.Injective f) :
    ∃ a v : ℝ,
    let w : ℝ := v - if 0 < v then 2 * Real.pi else -(2 * Real.pi)
    let inside : ℝ → Circle := fun t => Circle.exp (a + v * t)
    let outside : ℝ → Circle := fun t => Circle.exp (a + w * t)
    0 < |v| ∧ |v| < 2 * Real.pi ∧
    |w| = 2 * Real.pi - |v| ∧ 0 < |w| ∧ v * w < 0 ∧
    inside 0 = f 0 ∧ inside 1 = f 1 ∧
    outside 0 = f 0 ∧ outside 1 = f 1 ∧
    range f = inside '' Icc (0 : ℝ) 1 ∧
    f '' Ioo (0 : unitInterval) 1 = inside '' Ioo (0 : ℝ) 1 ∧
    (range f)ᶜ = outside '' Ioo (0 : ℝ) 1 ∧
    (f '' Ioo (0 : unitInterval) 1)ᶜ = outside '' Icc (0 : ℝ) 1 := by
  classical
  let x : Circle := f 0
  let y : Circle := f 1
  have hxy : x ≠ y := fun h => (by norm_num : (0 : unitInterval) ≠ 1) (hfi h)
  have hopen (g : unitInterval → Circle) (hi : Injective g) :
      g '' Ioo (0 : unitInterval) 1 = range g \ {g 0, g 1} := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨⟨t, rfl⟩, ?_⟩
      simp only [mem_insert_iff, mem_singleton_iff]
      rintro (h | h)
      · exact ht.1.ne' (hi h)
      · exact ht.2.ne (hi h)
    · rintro ⟨⟨t, rfl⟩, ht⟩
      simp only [mem_insert_iff, mem_singleton_iff, not_or] at ht
      exact ⟨t, ⟨unitInterval.pos_iff_ne_zero.mpr (fun h => ht.1 (congrArg g h)),
        unitInterval.lt_one_iff_ne_one.mpr (fun h => ht.2 (congrArg g h))⟩, rfl⟩
  have hrealClosed (g : ℝ → Circle) :
      range (fun t : unitInterval => g t) = g '' Icc (0 : ℝ) 1 := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.property, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  have hrealOpen (g : ℝ → Circle) :
      (fun t : unitInterval => g t) '' Ioo (0 : unitInterval) 1 =
        g '' Ioo (0 : ℝ) 1 := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht.1.le, ht.2.le⟩, ht, rfl⟩
  have hsymOpen (t : unitInterval) :
      unitInterval.symm t ∈ Ioo (0 : unitInterval) 1 ↔ t ∈ Ioo (0 : unitInterval) 1 := by
    change (0 < 1 - (t : ℝ) ∧ 1 - (t : ℝ) < 1) ↔ (0 < (t : ℝ) ∧ (t : ℝ) < 1)
    constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> linarith
  have hsymRange (g : unitInterval → Circle) : range (g ∘ unitInterval.symm) = range g := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨unitInterval.symm t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨unitInterval.symm t, by simp⟩
  have hsymImage (g : unitInterval → Circle) :
      (g ∘ unitInterval.symm) '' Ioo (0 : unitInterval) 1 = g '' Ioo (0 : unitInterval) 1 := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨unitInterval.symm t, (hsymOpen t).mpr ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨unitInterval.symm t, (hsymOpen t).mpr ht, by simp⟩
  have hfull (g : unitInterval → Circle) (hg : Continuous g) (hgi : Injective g)
      (hsub : range f ⊆ range g)
      (he : (f 0 = g 0 ∧ f 1 = g 1) ∨ (f 0 = g 1 ∧ f 1 = g 0)) :
      range f = range g := by
    let e : unitInterval ≃ₜ range g := (hg.isClosedEmbedding hgi).isEmbedding.toHomeomorph
    let z : unitInterval → unitInterval := fun t => e.symm ⟨f t, hsub ⟨t, rfl⟩⟩
    have hz : Continuous z := e.symm.continuous.comp (hf.subtype_mk _)
    have hrec (t : unitInterval) : g (z t) = f t :=
      congrArg Subtype.val (e.apply_symm_apply ⟨f t, hsub ⟨t, rfl⟩⟩)
    have hsurj : Surjective z := by
      intro t
      rcases he with he | he
      · have hz0 : z 0 = 0 := hgi ((hrec 0).trans he.1)
        have hz1 : z 1 = 1 := hgi ((hrec 1).trans he.2)
        have ht : t ∈ Icc (z 0) (z 1) := by
          rw [hz0, hz1]
          exact ⟨bot_le, le_top⟩
        obtain ⟨s, _, hs⟩ := intermediate_value_Icc (a := (0 : unitInterval))
          (b := 1) (by norm_num) hz.continuousOn ht
        exact ⟨s, hs⟩
      · have hz0 : z 0 = 1 := hgi ((hrec 0).trans he.1)
        have hz1 : z 1 = 0 := hgi ((hrec 1).trans he.2)
        have ht : t ∈ Icc (z 1) (z 0) := by
          rw [hz1, hz0]
          exact ⟨bot_le, le_top⟩
        obtain ⟨s, _, hs⟩ := intermediate_value_Icc' (a := (0 : unitInterval))
          (b := 1) (by norm_num) hz.continuousOn ht
        exact ⟨s, hs⟩
    refine Subset.antisymm hsub ?_
    rintro p ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := hsurj t
    exact ⟨s, (hrec s).symm.trans (congrArg g hs)⟩
  have hadd (T : Set Circle) (h₀ : x ∈ T) (h₁ : y ∈ T)
      (hi : f '' Ioo (0 : unitInterval) 1 ⊆ T) : range f ⊆ T := by
    rintro z ⟨t, rfl⟩
    by_cases ht0 : t = 0
    · simpa only [ht0] using h₀
    by_cases ht1 : t = 1
    · simpa only [ht1] using h₁
    exact hi ⟨t, ⟨unitInterval.pos_iff_ne_zero.mpr ht0,
      unitInterval.lt_one_iff_ne_one.mpr ht1⟩, rfl⟩
  have hpre : IsPreconnected (f '' Ioo (0 : unitInterval) 1) :=
    isPreconnected_Ioo.image f hf.continuousOn
  have hsep : (f '' Ioo (0 : unitInterval) 1) ∩
      (range (Circle.path x y) ∩ range (Circle.path y x)) = ∅ := by
    rw [Circle.range_path_inter_range_path hxy, hopen f hfi]
    ext z
    simp only [mem_inter_iff, mem_sdiff, mem_empty_iff_false, x, y]
    tauto
  have hparts := (isPreconnected_iff_subset_of_disjoint_closed.mp hpre)
    (range (Circle.path x y)) (range (Circle.path y x))
    (isCompact_range (Circle.path x y).continuous).isClosed
    (isCompact_range (Circle.path y x).continuous).isClosed
    (by rw [Circle.range_path_union_range_path hxy]; exact subset_univ _) hsep
  have hpath (z w : Circle) (t : unitInterval) :
      Circle.exp (Complex.arg (z : ℂ) + Circle.angleDiff z w * (t : ℝ)) = Circle.path z w t := by
    rw [Circle.path_apply, Path.segment_apply]
    congr 1
    simp only [AffineMap.lineMap_apply_ring]
    ring
  have hback (z w : Circle) (hzw : z ≠ w) (t : unitInterval) :
      Circle.exp (Complex.arg (z : ℂ) + (Circle.angleDiff z w - 2 * Real.pi) * (t : ℝ)) =
        Circle.path w z (unitInterval.symm t) := by
    have hd := Circle.angleDiff_add_angleDiff hzw
    have hb : Circle.exp (Complex.arg (w : ℂ) + Circle.angleDiff w z) = z := by
      rw [add_comm, Circle.exp_add, Circle.exp_arg, Circle.exp_angleDiff_mul]
    rw [← hpath, unitInterval.coe_symm_eq]
    calc
      _ = Circle.exp (Complex.arg (z : ℂ) + -(Circle.angleDiff w z * (t : ℝ))) := by
        have hs : Circle.angleDiff z w - 2 * Real.pi = -Circle.angleDiff w z := by linarith
        rw [hs]
        congr 1
        ring
      _ = z * Circle.exp (-(Circle.angleDiff w z * (t : ℝ))) := by
        rw [Circle.exp_add, Circle.exp_arg]
      _ = Circle.exp ((Complex.arg (w : ℂ) + Circle.angleDiff w z) +
          -(Circle.angleDiff w z * (t : ℝ))) := by rw [Circle.exp_add, hb]
      _ = _ := by congr 1; ring
  have dpos := Circle.angleDiff_pos hxy
  have epos := Circle.angleDiff_pos hxy.symm
  have dlt := Circle.angleDiff_lt_two_pi x y
  have elt := Circle.angleDiff_lt_two_pi y x
  have dsum := Circle.angleDiff_add_angleDiff hxy
  rcases hparts with hleft | hright
  · have hfr : range f = range (Circle.path x y) :=
      hfull _ (Circle.path x y).continuous (Circle.path_injective_of_ne hxy)
        (hadd _ (Circle.path x y).source_mem_range (Circle.path x y).target_mem_range hleft)
        (Or.inl ⟨(Circle.path x y).source.symm, (Circle.path x y).target.symm⟩)
    have hfo : f '' Ioo (0 : unitInterval) 1 = Circle.path x y '' Ioo (0 : unitInterval) 1 := by
      rw [hopen f hfi, hopen _ (Circle.path_injective_of_ne hxy), hfr]
      simp only [Path.source, Path.target, x, y]
    let inside : ℝ → Circle := fun t => Circle.exp (Complex.arg (x : ℂ) + Circle.angleDiff x y * t)
    let outside : ℝ → Circle := fun t =>
      Circle.exp (Complex.arg (x : ℂ) + (Circle.angleDiff x y - 2 * Real.pi) * t)
    have hi : (fun t : unitInterval => inside t) = Circle.path x y := funext (hpath x y)
    have ho : (fun t : unitInterval => outside t) = Circle.path y x ∘ unitInterval.symm :=
      funext (hback x y hxy)
    have hic : inside '' Icc (0 : ℝ) 1 = range (Circle.path x y) := by rw [← hrealClosed, hi]
    have hio : inside '' Ioo (0 : ℝ) 1 = Circle.path x y '' Ioo (0 : unitInterval) 1 := by
      rw [← hrealOpen, hi]
    have hoc : outside '' Icc (0 : ℝ) 1 = range (Circle.path y x) := by
      rw [← hrealClosed, ho, hsymRange]
    have hoo : outside '' Ioo (0 : ℝ) 1 = Circle.path y x '' Ioo (0 : unitInterval) 1 := by
      rw [← hrealOpen, ho, hsymImage]
    have hw : Circle.angleDiff x y - 2 * Real.pi < 0 := sub_neg.mpr dlt
    refine ⟨Complex.arg (x : ℂ), Circle.angleDiff x y, ?_⟩
    dsimp only
    rw [if_pos dpos]
    refine ⟨by simpa only [abs_of_pos dpos] using dpos,
      by simpa only [abs_of_pos dpos] using dlt, ?_, ?_, mul_neg_of_pos_of_neg dpos hw,
      ?_, ?_, ?_, ?_, hfr.trans hic.symm, hfo.trans hio.symm, ?_, ?_⟩
    · rw [abs_of_neg hw, abs_of_pos dpos]
      ring
    · exact abs_pos.mpr hw.ne
    · simpa only [Set.Icc.coe_zero, Path.source] using congrFun hi 0
    · simpa only [Set.Icc.coe_one, Path.target] using congrFun hi 1
    · simpa only [Set.Icc.coe_zero, comp_apply, unitInterval.symm_zero, Path.target] using
        congrFun ho 0
    · simpa only [Set.Icc.coe_one, comp_apply, unitInterval.symm_one, Path.source] using
        congrFun ho 1
    · rw [hfr, hoo]
      exact Circle.compl_range_path hxy
    · rw [hfo, hoc]
      rw [← Circle.compl_range_path hxy.symm, compl_compl]
  · have hfr : range f = range (Circle.path y x) :=
      hfull _ (Circle.path y x).continuous (Circle.path_injective_of_ne hxy.symm)
        (hadd _ (Circle.path y x).target_mem_range (Circle.path y x).source_mem_range hright)
        (Or.inr ⟨(Circle.path y x).target.symm, (Circle.path y x).source.symm⟩)
    have hfo : f '' Ioo (0 : unitInterval) 1 = Circle.path y x '' Ioo (0 : unitInterval) 1 := by
      rw [hopen f hfi, hopen _ (Circle.path_injective_of_ne hxy.symm), hfr]
      simp only [Path.source, Path.target, x, y, Set.pair_comm]
    let a : ℝ := Complex.arg (y : ℂ) + Circle.angleDiff y x
    let inside : ℝ → Circle := fun t => Circle.exp (a + (-Circle.angleDiff y x) * t)
    let outside : ℝ → Circle := fun t =>
      Circle.exp (a + (-Circle.angleDiff y x + 2 * Real.pi) * t)
    have hi : (fun t : unitInterval => inside t) = Circle.path y x ∘ unitInterval.symm := by
      funext t
      rw [comp_apply, ← hpath, unitInterval.coe_symm_eq]
      change Circle.exp (Complex.arg (y : ℂ) + Circle.angleDiff y x +
        -Circle.angleDiff y x * (t : ℝ)) = _
      congr 1
      ring
    have ha : Circle.exp a = x := by
      dsimp [a]
      rw [add_comm, Circle.exp_add, Circle.exp_arg, Circle.exp_angleDiff_mul]
    have ho : (fun t : unitInterval => outside t) = Circle.path x y := by
      funext t
      rw [← hpath]
      change Circle.exp (a + (-Circle.angleDiff y x + 2 * Real.pi) * (t : ℝ)) = _
      have hv : -Circle.angleDiff y x + 2 * Real.pi = Circle.angleDiff x y := by linarith
      rw [hv, Circle.exp_add, ha, Circle.exp_add, Circle.exp_arg]
    have hic : inside '' Icc (0 : ℝ) 1 = range (Circle.path y x) := by
      rw [← hrealClosed, hi, hsymRange]
    have hio : inside '' Ioo (0 : ℝ) 1 = Circle.path y x '' Ioo (0 : unitInterval) 1 := by
      rw [← hrealOpen, hi, hsymImage]
    have hoc : outside '' Icc (0 : ℝ) 1 = range (Circle.path x y) := by rw [← hrealClosed, ho]
    have hoo : outside '' Ioo (0 : ℝ) 1 = Circle.path x y '' Ioo (0 : unitInterval) 1 := by
      rw [← hrealOpen, ho]
    have hv : ¬0 < -Circle.angleDiff y x := by linarith
    have hw : 0 < -Circle.angleDiff y x + 2 * Real.pi := by linarith
    refine ⟨a, -Circle.angleDiff y x, ?_⟩
    dsimp only
    rw [if_neg hv, sub_neg_eq_add]
    refine ⟨by simpa only [abs_neg, abs_of_pos epos] using epos,
      by simpa only [abs_neg, abs_of_pos epos] using elt, ?_,
      abs_pos.mpr hw.ne', mul_neg_of_neg_of_pos (by linarith) hw,
      ?_, ?_, ?_, ?_, hfr.trans hic.symm, hfo.trans hio.symm, ?_, ?_⟩
    · rw [abs_of_pos hw, abs_neg, abs_of_pos epos]
      ring
    · simpa only [Set.Icc.coe_zero, comp_apply, unitInterval.symm_zero, Path.target] using
        congrFun hi 0
    · simpa only [Set.Icc.coe_one, comp_apply, unitInterval.symm_one, Path.source] using
        congrFun hi 1
    · simpa only [Set.Icc.coe_zero, Path.source] using congrFun ho 0
    · simpa only [Set.Icc.coe_one, Path.target] using congrFun ho 1
    · rw [hfr, hoo]
      exact Circle.compl_range_path hxy.symm
    · rw [hfo, hoc]
      rw [← Circle.compl_range_path hxy, compl_compl]

end PoincareConjecture.M25.Topology3D
