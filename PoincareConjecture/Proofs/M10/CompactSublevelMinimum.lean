import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

open Set

namespace PoincareConjecture.M10

variable {X A : Type*} [TopologicalSpace X] [TopologicalSpace A]

theorem exists_global_minimum_of_compact_sublevel {f : X → ℝ} (hf : Continuous f)
    {K : Set X} (hK : IsCompact K) {L : ℝ}
    (hsub : ∀ x, f x ≤ L → x ∈ K) (hcomp : ∃ x, f x ≤ L) :
    ∃ x ∈ K, (∀ y, f x ≤ f y) ∧ f x = sInf (range f) := by
  obtain ⟨z, hz⟩ := hcomp
  have hzK := hsub z hz
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn ⟨z, hzK⟩ hf.continuousOn
  have hglobal (y : X) : f x ≤ f y := by
    by_cases hy : f y ≤ L
    · exact hmin (hsub y hy)
    · exact (hmin hzK).trans (hz.trans (le_of_not_ge hy))
  refine ⟨x, hx, hglobal, ?_⟩
  apply Eq.symm
  apply IsLeast.csInf_eq
  refine ⟨mem_range_self x, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact hglobal y

theorem continuous_sInf_of_compact_sublevels {f : A → X → ℝ}
    (hf : Continuous (fun z : A × X ↦ f z.1 z.2))
    {K : Set X} (hK : IsCompact K) {L : ℝ}
    (hsub : ∀ a x, f a x ≤ L → x ∈ K) (hcomp : ∀ a, ∃ x, f a x ≤ L) :
    Continuous (fun a ↦ sInf (range (f a))) := by
  have heq (a : A) : sInf (range (f a)) = sInf (f a '' K) := by
    obtain ⟨x, hx, hmin, hval⟩ := exists_global_minimum_of_compact_sublevel (f := f a)
      (hf.comp (continuous_const.prodMk continuous_id)) hK (hsub a) (hcomp a)
    rw [← hval]
    apply Eq.symm
    apply IsLeast.csInf_eq
    refine ⟨mem_image_of_mem _ hx, ?_⟩
    rintro _ ⟨y, _, rfl⟩
    exact hmin y
  simp_rw [heq]
  exact hK.continuous_sInf hf

end PoincareConjecture.M10
