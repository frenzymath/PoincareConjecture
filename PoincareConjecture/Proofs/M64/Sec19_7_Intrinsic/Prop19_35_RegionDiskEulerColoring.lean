import PoincareConjecture.Proofs.Horizon.Topology.Surface.Combinatorial.Incidence
import Mathlib.Topology.Connected.Basic












set_option autoImplicit false

open Set
open PoincareConjecture.Surface.Combinatorial.Incidence

namespace PoincareConjecture

private lemma m64_exists_closed_cover_member_of_mem_closure
    {X I : Type*} [TopologicalSpace X] [Finite I]
    (A : I → Set X) (hclosed : ∀ i, IsClosed (A i)) (P : I → Prop)
    {S : Set X} (hsub : S ⊆ ⋃ i, ⋃ (_ : P i), A i) {p : X}
    (hp : p ∈ closure S) : ∃ i, p ∈ A i ∧ P i := by
  have hc : IsClosed (⋃ i, ⋃ (_ : P i), A i) :=
    isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun _ => hclosed i
  obtain ⟨i, hi⟩ := mem_iUnion.mp (closure_minimal hsub hc hp)
  obtain ⟨hPi, hpAi⟩ := mem_iUnion.mp hi
  exact ⟨i, hpAi, hPi⟩






theorem m64Intrinsic_exists_jordan_cell_coloring
    {X I : Type*} [TopologicalSpace X] [Finite I]
    (A : I → Set X) (hclosed : ∀ i, IsClosed (A i))
    (hregular : ∀ i, closure (interior (A i)) = A i)
    (hconnected : ∀ i, IsPreconnected (interior (A i)))
    (hcover : (⋃ i, A i) = univ)
    {K U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hdisjoint : Disjoint U V)
    (hpartition : U ∪ V = Kᶜ) (hfrontU : frontier U = K) (hfrontV : frontier V = K)
    (havoid : ∀ i, Disjoint (interior (A i)) K) :
    ∃ color : I → Bool, ∀ (i j : I) (p : X),
      (∀ k, p ∈ A k ↔ k = i ∨ k = j) →
      (color i ≠ color j ↔ p ∈ K) := by
  classical
  let P (i : I) : Prop := interior (A i) ⊆ U
  have hside (i : I) : P i ∨ interior (A i) ⊆ V := by
    apply (hconnected i).subset_or_subset hU hV hdisjoint
    rw [hpartition]
    exact disjoint_left.mp (havoid i)
  have hsideV (i : I) (hi : ¬ P i) : interior (A i) ⊆ V := (hside i).resolve_left hi
  have hAU (i : I) (hi : P i) : A i ⊆ closure U := by
    rw [← hregular i]
    exact closure_mono hi
  have hAV (i : I) (hi : ¬ P i) : A i ⊆ closure V := by
    rw [← hregular i]
    exact closure_mono (hsideV i hi)
  have hmemU (i : I) {p : X} (hp : p ∈ U) (hpi : p ∈ A i) : P i := by
    by_contra hi
    exact disjoint_left.mp (hdisjoint.closure_right hU) hp (hAV i hi hpi)
  have hmemV (i : I) {p : X} (hp : p ∈ V) (hpi : p ∈ A i) : ¬ P i := by
    intro hi
    exact disjoint_left.mp (hdisjoint.closure_left hV) (hAU i hi hpi) hp
  have hUsub : U ⊆ ⋃ i, ⋃ (_ : P i), A i := by
    intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ p)
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hmemU i hp hi, hi⟩⟩
  have hVsub : V ⊆ ⋃ i, ⋃ (_ : ¬ P i), A i := by
    intro p hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ p)
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hmemV i hp hi, hi⟩⟩
  let color (i : I) : Bool := if P i then true else false
  refine ⟨color, ?_⟩
  intro i j p hinc
  have hpi : p ∈ A i := (hinc i).mpr (Or.inl rfl)
  have hpj : p ∈ A j := (hinc j).mpr (Or.inr rfl)
  constructor
  · intro hne
    by_contra hp
    have hpUV : p ∈ U ∪ V := hpartition.symm ▸ hp
    rcases hpUV with hpU | hpV
    · exact hne (by simp only [color, if_pos (hmemU i hpU hpi),
        if_pos (hmemU j hpU hpj)])
    · exact hne (by simp only [color, if_neg (hmemV i hpV hpi),
        if_neg (hmemV j hpV hpj)])
  · intro hp
    obtain ⟨k, hpk, hk⟩ := m64_exists_closed_cover_member_of_mem_closure A hclosed P
      hUsub (frontier_subset_closure (hfrontU.symm ▸ hp))
    obtain ⟨l, hpl, hl⟩ := m64_exists_closed_cover_member_of_mem_closure A hclosed
      (fun a => ¬ P a) hVsub (frontier_subset_closure (hfrontV.symm ▸ hp))
    have hkcolor : color k = true := by simp only [color, if_pos hk]
    have hlcolor : color l = false := by simp only [color, if_neg hl]
    intro heq
    rcases (hinc k).mp hpk with hki | hkj <;>
      rcases (hinc l).mp hpl with hli | hlj <;>
      simp_all only [Bool.true_eq_false]





theorem m64Intrinsic_region_cycle_fill_of_jordan_partition
    {X I E : Type*} [TopologicalSpace X] [Fintype I]
    (A : I → Set X) (hclosed : ∀ i, IsClosed (A i))
    (hregular : ∀ i, closure (interior (A i)) = A i)
    (hconnected : ∀ i, IsPreconnected (interior (A i)))
    (hcover : (⋃ i, A i) = univ)
    {K U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hdisjoint : Disjoint U V)
    (hpartition : U ∪ V = Kᶜ) (hfrontU : frontier U = K) (hfrontV : frontier V = K)
    (havoid : ∀ i, Disjoint (interior (A i)) K)
    (adjacent : E → I × I) (midpoint : E → X)
    (hinc : ∀ e i, midpoint e ∈ A i ↔ i = (adjacent e).1 ∨ i = (adjacent e).2)
    (x : E → ZMod 2) (hselected : ∀ e, midpoint e ∈ K ↔ x e ≠ 0) :
    x ∈ LinearMap.range (incidenceMatrix adjacent).mulVecLin := by
  classical
  obtain ⟨color, hcolor⟩ := m64Intrinsic_exists_jordan_cell_coloring A hclosed
    hregular hconnected hcover hU hV hdisjoint hpartition hfrontU hfrontV havoid
  refine ⟨fun i => if color i then 1 else 0, ?_⟩
  funext e
  change (incidenceMatrix adjacent).mulVec (fun i => if color i then 1 else 0) e = x e
  rw [incidenceMatrix_mulVec_apply]
  have hdiff := (hcolor (adjacent e).1 (adjacent e).2 (midpoint e) (hinc e)).trans
    (hselected e)
  have hbinary : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  cases hi : color (adjacent e).1 <;> cases hj : color (adjacent e).2 <;>
    rcases hbinary (x e) with hx | hx <;>
    simp_all [CharTwo.add_self_eq_zero]

end PoincareConjecture
