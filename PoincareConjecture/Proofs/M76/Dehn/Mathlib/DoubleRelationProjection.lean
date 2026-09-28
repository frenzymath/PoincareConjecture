import Mathlib.Data.Set.Card











set_option autoImplicit false

open Set





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
