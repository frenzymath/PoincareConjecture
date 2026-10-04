import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Avoiding countably many forbidden preimages in a real interval

The regular-time attachment in Morgan--Tian Claim 11.35, printed
pp. 289-291, uses one normalized time for the whole sequence. Countable
preimages under injective maps have dense complement, even when their
codomains vary. Reviewed derivation: `claim11_35-common-regular-time.md`.
-/

set_option autoImplicit false

open Set

universe u v

namespace PoincareMT.M32

/-- A real interval contains a point avoiding a countable family of
countable forbidden sets through injective maps. This is the regular-time
selection used in Claim 11.35, printed pp. 289-291. -/
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

end PoincareMT.M32
