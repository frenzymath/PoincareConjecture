import PoincareConjecture.Proofs.M76.Mathlib.AffineSubspaceAvoidance
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Set.Infinite











set_option autoImplicit false

open Set

namespace AffineSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





theorem exists_avoiding_directions [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι] (A : ι → AffineSubspace ℝ E)
    (hA : ∀ i, A i ≠ ⊤) :
    ∃ u : E, ∀ i, (A i : Set E).Nonempty → u ∉ (A i).direction := by
  let T := {i : ι // (A i : Set E).Nonempty}
  let B : T → AffineSubspace ℝ E := fun i => (A i.val).direction.toAffineSubspace
  have hB : ∀ i, B i ≠ ⊤ := by
    intro i hi
    have hd : (A i.val).direction = ⊤ := by
      apply top_unique
      intro x _
      change x ∈ B i
      rw [hi]
      trivial
    exact hA i.val ((direction_eq_top_iff_of_nonempty i.property).mp hd)
  obtain ⟨u, hu⟩ := (dense_compl_iUnion B hB).nonempty
  refine ⟨u, ?_⟩
  intro i hi hui
  exact hu (mem_iUnion.mpr ⟨⟨i, hi⟩, hui⟩)





theorem subsingleton_line_parameters (A : AffineSubspace ℝ E) (v u : E)
    (hu : (A : Set E).Nonempty → u ∉ A.direction) :
    {t : ℝ | v + t • u ∈ A}.Subsingleton := by
  intro a ha b hb
  by_contra hab
  apply hu ⟨v + a • u, ha⟩
  have hsub : (a - b) • u ∈ A.direction := by
    simpa only [vsub_eq_sub, add_sub_add_left_eq_sub, ← sub_smul] using
      vsub_mem_direction ha hb
  exact (A.direction.smul_mem_iff (sub_ne_zero.mpr hab)).mp hsub





theorem exists_pos_small_line_avoiding
    {ι : Type*} [Finite ι] (A : ι → AffineSubspace ℝ E) (v u : E)
    (hu : ∀ i, (A i : Set E).Nonempty → u ∉ (A i).direction)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : ℝ, a ∈ Ioo 0 ε ∧ ∀ i, v + a • u ∉ A i := by
  have hfinite : (⋃ i, {t : ℝ | v + t • u ∈ A i}).Finite :=
    finite_iUnion (fun i => ((A i).subsingleton_line_parameters v u (hu i)).finite)
  obtain ⟨a, ha, havoid⟩ := (Ioo_infinite hε).exists_notMem_finite hfinite
  exact ⟨a, ha, fun i hi => havoid (mem_iUnion.mpr ⟨i, hi⟩)⟩

end AffineSubspace
