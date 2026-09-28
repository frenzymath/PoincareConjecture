import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Compactness.Compact









set_option autoImplicit false

open Set

namespace BrownCollar

variable {X Y ι : Type*} [TopologicalSpace X]




theorem exists_open_ambient_agreement [Finite ι]
    (S : Set X) (O U : ι → Set X) (g : ι → X → Y)
    (hclosure : ∀ i, closure (U i) ⊆ O i)
    (hlocal : ∀ i j x, x ∈ S → x ∈ O i ∩ O j →
      ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ EqOn (g i) (g j) V) :
    ∃ N : Set X, IsOpen N ∧ S ⊆ N ∧
      ∀ i j, EqOn (g i) (g j) (N ∩ U i ∩ U j) := by
  let bad : ι → ι → Set X := fun i j => U i ∩ U j ∩ {x | g i x ≠ g j x}
  have hnot (i j : ι) (x : X) (hx : x ∈ S) : x ∉ closure (bad i j) := by
    intro hxb
    have hbi : bad i j ⊆ U i := fun _ h => h.1.1
    have hbj : bad i j ⊆ U j := fun _ h => h.1.2
    have hxi : x ∈ O i := hclosure i (closure_mono hbi hxb)
    have hxj : x ∈ O j := hclosure j (closure_mono hbj hxb)
    obtain ⟨V, hV, hxV, hEq⟩ := hlocal i j x hx ⟨hxi, hxj⟩
    obtain ⟨y, hyV, hyb⟩ := mem_closure_iff.mp hxb V hV hxV
    exact hyb.2 (hEq hyV)
  let N := (⋃ i, ⋃ j, closure (bad i j))ᶜ
  have hN : IsOpen N :=
    (isClosed_iUnion_of_finite (fun i : ι =>
      isClosed_iUnion_of_finite (fun j : ι =>
        isClosed_closure (s := bad i j)))).isOpen_compl
  refine ⟨N, hN, ?_, ?_⟩
  · intro x hx hbad
    obtain ⟨i, hi⟩ := mem_iUnion.mp hbad
    obtain ⟨j, hj⟩ := mem_iUnion.mp hi
    exact hnot i j x hx hj
  · intro i j x hx
    by_contra hne
    have hxb : x ∈ bad i j := ⟨⟨hx.1.2, hx.2⟩, hne⟩
    exact hx.1.1 (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, subset_closure hxb⟩⟩)



theorem exists_finite_shrunken_cover [T1Space X] [NormalSpace X]
    {S : Set X} (hS : IsCompact S) (O : ι → Set X) (hO : ∀ i, IsOpen (O i))
    (a : S → ι) (ha : ∀ x : S, (x : X) ∈ O (a x)) :
    ∃ (U : S → Set X) (t : Finset S),
      (∀ x, IsOpen (U x) ∧ (x : X) ∈ U x ∧ closure (U x) ⊆ O (a x)) ∧
      S ⊆ ⋃ x ∈ t, U x := by
  classical
  have haux (x : S) : ∃ U : Set X,
      IsOpen U ∧ (x : X) ∈ U ∧ closure U ⊆ O (a x) := by
    obtain ⟨U, hU, hxU, hcl⟩ := normal_exists_closure_subset
      (isClosed_singleton (x := (x : X))) (hO (a x)) (singleton_subset_iff.mpr (ha x))
    exact ⟨U, hU, hxU (mem_singleton _), hcl⟩
  choose U hU hxU hcl using haux
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover U hU (fun x hx =>
    mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩)
  exact ⟨U, t, fun x => ⟨hU x, hxU x, hcl x⟩, ht⟩

end BrownCollar
