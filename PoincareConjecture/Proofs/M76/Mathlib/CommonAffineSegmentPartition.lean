import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalPartition
import PoincareConjecture.Proofs.M76.Mathlib.FiniteOrderedPartition

set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem FinitePiecewiseAffineOn.exists_common_affine_segment_partition
    {f : E → F} {s : Set E} (hf : FinitePiecewiseAffineOn f s)
    {ι : Type*} [Finite ι] (a : ι → ℝ →ᴬ[ℝ] E)
    (ha : ∀ i, MapsTo (a i) (Icc (0 : ℝ) 1) s) :
    ∃ (n : ℕ) (t : Fin (n + 2) → ℝ), StrictMono t ∧ t 0 = 0 ∧
      t (Fin.last (n + 1)) = 1 ∧
      ∀ (i : ι) (j : Fin (n + 1)), ∃ A : ℝ →ᴬ[ℝ] F,
        EqOn (f ∘ a i) A (Icc (t j.castSucc) (t j.succ)) := by
  classical
  let := Fintype.ofFinite ι
  choose B hB hB0 hB1 hformula using fun i => hf.exists_affine_segment_breakpoints (a i) (ha i)
  let T := Finset.univ.biUnion B ∪ {0, 1}
  have hBT (i : ι) : (B i : Set ℝ) ⊆ T := fun x hx =>
    Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩)
  have hT : (T : Set ℝ) ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
      exact hB i hxi
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨le_rfl, zero_le_one⟩
      · rw [Finset.mem_singleton.mp hx]
        exact ⟨zero_le_one, le_rfl⟩
  obtain ⟨n, t, ht, ht0, ht1, hrange, hgap⟩ := T.exists_ordered_partition zero_lt_one hT
    (Finset.mem_union_right _ (Finset.mem_insert_self _ _))
    (Finset.mem_union_right _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
  refine ⟨n, t, ht, ht0, ht1, fun i j => ?_⟩
  have hmem (k : Fin (n + 2)) : t k ∈ Icc (0 : ℝ) 1 :=
    hT (hrange ▸ mem_range_self k)
  exact hformula i _ _ (hmem j.castSucc).1 (hmem j.succ).2
    (ht Fin.castSucc_lt_succ) ((hgap j).mono_right (hBT i))

end Geometry
