import Mathlib.Data.Set.Card

/-!
# Injective coordinate projection of a two-point-fiber relation

Two distinct points exhaust their actual finite fiber when its
cardinality is at most two. Consequently the first coordinate
determines the whole distinct-point pair. This is the source
projection used in Dehn032, section7, without any ambient deck
transformation or global two-sheet assertion.
-/

set_option autoImplicit false

open Set

/-- Finite fibers of cardinality at most two make the first
projection injective on the actual distinct-point relation.
Finiteness is retained separately because ncard alone does not
exclude infinite fibers. See Dehn032, section7. -/
theorem Function.injOn_fst_double_relation
    {X Y : Type*} {f : X → Y}
    (hf : ∀ y, (f ⁻¹' {y}).Finite) (hn : ∀ y, (f ⁻¹' {y}).ncard ≤ 2) :
    InjOn Prod.fst {z : X × X | f z.1 = f z.2 ∧ z.1 ≠ z.2} := by
  intro z hz w hw hfirst
  have hpair : ({z.1, z.2} : Set X) ⊆ f ⁻¹' {f z.1} := by
    intro x hx
    rcases mem_insert_iff.mp hx with rfl | hx
    · rfl
    · rw [mem_singleton_iff] at hx
      subst x
      exact hz.1.symm
  have hwhole : ({z.1, z.2} : Set X) = f ⁻¹' {f z.1} :=
    eq_of_subset_of_ncard_le hpair (by rw [ncard_pair hz.2]; exact hn (f z.1)) (hf _)
  have hwsecond : w.2 ∈ ({z.1, z.2} : Set X) :=
    hwhole.superset (hw.1.symm.trans (congrArg f hfirst.symm))
  rcases mem_insert_iff.mp hwsecond with heq | heq
  · exact False.elim (hw.2 (hfirst.symm.trans heq.symm))
  · exact Prod.ext hfirst (mem_singleton_iff.mp heq).symm
