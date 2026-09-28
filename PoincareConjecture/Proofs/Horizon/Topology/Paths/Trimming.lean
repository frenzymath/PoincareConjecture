import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

set_option autoImplicit false

open Set
open scoped Topology

namespace Poincare.Topology

variable {X : Type*} [TopologicalSpace X]

theorem exists_arc_trimming {f : ℝ → X} (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    {U V : Set X} (hU : U ∈ 𝓝 (f 0)) (hV : V ∈ 𝓝 (f 1)) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ b < 1 ∧
      f '' Icc 0 a ⊆ U ∧ f '' Icc b 1 ⊆ V := by
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhdsWithin_iff.mp
    ((hf 0 (by norm_num)).preimage_mem_nhdsWithin hU)
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhdsWithin_iff.mp
    ((hf 1 (by norm_num)).preimage_mem_nhdsWithin hV)
  let a := min ε (1 / 3) / 2
  let b := 1 - min δ (1 / 3) / 2
  have ha : 0 < a := half_pos (lt_min hε (by norm_num))
  have haε : a < ε := by dsimp [a]; linarith [min_le_left ε (1 / 3)]
  have ha₃ : a ≤ 1 / 6 := by dsimp [a]; linarith [min_le_right ε (1 / 3)]
  have hb : b < 1 := by
    have h := half_pos (lt_min hδ (by norm_num : (0 : ℝ) < 1 / 3))
    dsimp [b]
    linarith
  have hbδ : 1 - b < δ := by dsimp [b]; linarith [min_le_left δ (1 / 3)]
  have hb₃ : 5 / 6 ≤ b := by dsimp [b]; linarith [min_le_right δ (1 / 3)]
  refine ⟨a, b, ha, by linarith, hb, ?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    apply hεU
    refine ⟨?_, ht.1, by linarith [ht.2]⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact ht.2.trans_lt haε
  · rintro _ ⟨t, ht, rfl⟩
    apply hδV
    refine ⟨?_, by linarith [ht.1], ht.2⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith [ht.2])]
    linarith [ht.1]

omit [TopologicalSpace X] in

theorem disjoint_arc_interior_of_endpoint_intersections {f g : ℝ → X}
    (hf : InjOn f (Icc (0 : ℝ) 1))
    (hfg : f '' Icc (0 : ℝ) 1 ∩ g '' Icc (0 : ℝ) 1 ⊆ {f 0, f 1}) :
    Disjoint (f '' Ioo (0 : ℝ) 1) (g '' Icc (0 : ℝ) 1) := by
  apply disjoint_left.mpr
  rintro _ ⟨t, ht, rfl⟩ hg
  rcases Set.mem_insert_iff.mp (hfg ⟨⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩, hg⟩) with h | h
  · have heq := hf ⟨ht.1.le, ht.2.le⟩ (by norm_num) h
    exact ht.1.ne' heq
  · have heq := hf ⟨ht.1.le, ht.2.le⟩ (by norm_num) (mem_singleton_iff.mp h)
    exact ht.2.ne heq

theorem exists_disjoint_compact_arc_cores {I : Type*} (f : I → ℝ → X)
    (hf : ∀ i, ContinuousOn (f i) (Icc (0 : ℝ) 1))
    (hinj : ∀ i, InjOn (f i) (Icc (0 : ℝ) 1))
    (hmeet : ∀ i j, i ≠ j →
      f i '' Icc (0 : ℝ) 1 ∩ f j '' Icc (0 : ℝ) 1 ⊆ {f i 0, f i 1})
    (U V : I → Set X) (hU : ∀ i, U i ∈ 𝓝 (f i 0))
    (hV : ∀ i, V i ∈ 𝓝 (f i 1)) :
    ∃ a b : I → ℝ,
      (∀ i, 0 < a i ∧ a i < b i ∧ b i < 1) ∧
      (∀ i, f i '' Icc 0 (a i) ⊆ U i ∧ f i '' Icc (b i) 1 ⊆ V i) ∧
      (∀ i, IsCompact (f i '' Icc (a i) (b i))) ∧
      (∀ i j, i ≠ j → Disjoint (f i '' Icc (a i) (b i)) (f j '' Icc 0 1)) ∧
      (∀ i, f i '' Icc (0 : ℝ) 1 =
        f i '' Icc 0 (a i) ∪ f i '' Icc (a i) (b i) ∪ f i '' Icc (b i) 1) := by
  choose a b ha hab hb hhead htail using fun i => exists_arc_trimming (hf i) (hU i) (hV i)
  have hsub (i : I) : Icc (a i) (b i) ⊆ Icc (0 : ℝ) 1 :=
    Icc_subset_Icc (ha i).le (hb i).le
  refine ⟨a, b, fun i => ⟨ha i, hab i, hb i⟩, fun i => ⟨hhead i, htail i⟩,
    fun i => isCompact_Icc.image_of_continuousOn ((hf i).mono (hsub i)), ?_, ?_⟩
  · intro i j hij
    exact (disjoint_arc_interior_of_endpoint_intersections (hinj i) (hmeet i j hij)).mono_left
      (image_mono (show Icc (a i) (b i) ⊆ Ioo (0 : ℝ) 1 from
        fun t ht => ⟨(ha i).trans_le ht.1, ht.2.trans_lt (hb i)⟩))
  · intro i
    rw [← image_union, ← image_union]
    congr 1
    ext t
    simp only [mem_Icc, mem_union]
    constructor
    · intro ht
      by_cases hta : t ≤ a i
      · exact Or.inl (Or.inl ⟨ht.1, hta⟩)
      · by_cases htb : t ≤ b i
        · exact Or.inl (Or.inr ⟨(lt_of_not_ge hta).le, htb⟩)
        · exact Or.inr ⟨(lt_of_not_ge htb).le, ht.2⟩
    · rintro ((ht | ht) | ht)
      · exact ⟨ht.1, ht.2.trans (hab i).le |>.trans (hb i).le⟩
      · exact hsub i ht
      · exact ⟨(ha i).le.trans ((hab i).le.trans ht.1), ht.2⟩

end Poincare.Topology
