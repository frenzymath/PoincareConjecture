import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Analysis.Convex.Join
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

set_option autoImplicit false

open Set

namespace Submodule

set_option maxHeartbeats 800000 in

theorem exists_ne_zero_forall_notMem_span_pair
    {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    (hdim : 2 < Module.finrank ℝ E) (a b : ι → E) :
    ∃ y : E, y ≠ 0 ∧ ∀ i, y ∉ span ℝ ({a i, b i} : Set E) := by
  classical
  have hproper (x z : E) : span ℝ ({x, z} : Set E) ≠ ⊤ := by
    have hdimPair : Module.finrank ℝ (span ℝ ({x, z} : Set E)) ≤ 2 := by
      have hcard := finrank_span_finset_le_card (R := ℝ) ({x, z} : Finset E)
      simp only [Finset.coe_pair] at hcard
      exact hcard.trans Finset.card_le_two
    intro heq
    rw [heq, finrank_top] at hdimPair
    omega
  let S : Option ι → Submodule ℝ E := fun i =>
    match i with
    | none => span ℝ ({0, 0} : Set E)
    | some j => span ℝ ({a j, b j} : Set E)
  obtain ⟨y, hy⟩ := exists_forall_notMem_of_forall_ne_top S (fun i => by
    cases i with
    | none => exact hproper 0 0
    | some j => exact hproper (a j) (b j))
  refine ⟨y, ?_, fun i => hy (some i)⟩
  intro hy0
  apply hy none
  rw [hy0]
  exact (S none).zero_mem

end Submodule

theorem zero_notMem_convexHull_triple_of_notMem_span_pair
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {a b y : E} (hedge : (0 : E) ∉ segment ℝ a b)
    (hy : y ∉ Submodule.span ℝ ({a, b} : Set E)) :
    (0 : E) ∉ convexHull ℝ ({y, a, b} : Set E) := by
  intro hzero
  rw [← convexJoin_singleton_segment] at hzero
  obtain ⟨z, hz, x, hx, hseg⟩ := mem_convexJoin.mp hzero
  have hzy : z = y := mem_singleton_iff.mp hz
  subst z
  obtain ⟨s, t, _, _, hst, heq⟩ := hseg
  by_cases hs : s = 0
  · have ht : t = 1 := by simpa [hs] using hst
    have hx0 : x = 0 := by simpa [hs, ht] using heq
    exact hedge (hx0 ▸ hx)
  · let S := Submodule.span ℝ ({a, b} : Set E)
    have hxS : x ∈ S := S.convex.segment_subset
      (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp)) hx
    have hsy : s • y = 0 - t • x := by
      rw [eq_sub_iff_add_eq]
      exact heq
    have hsyS : s • y ∈ S := by
      rw [hsy]
      exact S.sub_mem S.zero_mem (S.smul_mem t hxS)
    exact hy ((S.smul_mem_iff hs).mp hsyS)

theorem exists_ne_zero_forall_zero_notMem_convexHull_triple
    {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    (hdim : 2 < Module.finrank ℝ E) (a b : ι → E)
    (hedge : ∀ i, (0 : E) ∉ segment ℝ (a i) (b i)) :
    ∃ y : E, y ≠ 0 ∧ ∀ i, (0 : E) ∉ convexHull ℝ ({y, a i, b i} : Set E) := by
  obtain ⟨y, hy0, hy⟩ := Submodule.exists_ne_zero_forall_notMem_span_pair hdim a b
  exact ⟨y, hy0, fun i => zero_notMem_convexHull_triple_of_notMem_span_pair
    (hedge i) (hy i)⟩
