import Mathlib.Topology.Algebra.Module.Cardinality

set_option autoImplicit false

open Set

universe u v

namespace PoincareConjecture.M32

theorem exists_between_avoiding_countable_preimages
    {I : Type u} [Countable I] {Y : I → Type v}
    (D : ∀ i, Set (Y i)) (hD : ∀ i, (D i).Countable)
    (f : ∀ i, ℝ → Y i) (hf : ∀ i, Function.Injective (f i))
    {a b : ℝ} (hab : a < b) :
    ∃ t : ℝ, t ∈ Ioo a b ∧ ∀ i, f i t ∉ D i := by
  have hcount : (⋃ i, (f i) ⁻¹' D i).Countable :=
    countable_iUnion fun i => (hD i).preimage (hf i)
  obtain ⟨t, havoid, ht⟩ := (hcount.dense_compl ℝ).exists_mem_open
    isOpen_Ioo (nonempty_Ioo.mpr hab)
  refine ⟨t, ht, ?_⟩
  intro i hi
  exact havoid (mem_iUnion.mpr ⟨i, hi⟩)

end PoincareConjecture.M32
