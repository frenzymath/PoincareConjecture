import PoincareConjecture.Proofs.M02.Topology.IntegralSupportMayerVietoris










set_option autoImplicit false

noncomputable section

open CategoryTheory Limits HomologicalComplex

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X]

theorem integralSupportHomology_empty_isZero (n : Nat) :
    IsZero (integralSupportHomology (∅ : Set X) n) := by
  let e : TopCat.of (Set.univ : Set X) ≅ TopCat.of X :=
    TopCat.isoOfHomeo (Homeomorph.Set.univ X)
  have : IsIso (integralSubspaceChains (Set.univ : Set X)) := by
    change IsIso (integralChainsFunctor.map e.hom)
    infer_instance
  change IsZero ((integralRelativeChains (∅ : Set X)ᶜ).homology n)
  rw [Set.compl_empty]
  exact (homologyFunctor (ModuleCat.{u} Int) (ComplexShape.down Nat) n).map_isZero
    (isZero_cokernel_of_epi (integralSubspaceChains (Set.univ : Set X)))

theorem integralSupportHomology_finset_union_isZero
    {ι : Type v} (s : Finset ι) (F : ι → Set X) (d : Nat)
    (hF : ∀ i ∈ s, IsClosed (F i))
    (hI : ∀ t : Finset ι, t ⊆ s → t.Nonempty → ∀ n : Nat,
      IsZero (integralSupportHomology (⋂ i ∈ t, F i) (n + d))) :
    ∀ n : Nat, IsZero (integralSupportHomology (⋃ i ∈ s, F i) (n + d)) := by
  classical
  induction s using Finset.induction_on generalizing F with
  | empty =>
      intro n
      simpa using (integralSupportHomology_empty_isZero (X := X) (n + d))
  | @insert a s ha ih =>
      intro n
      have hrest : ∀ i ∈ s, IsClosed (F i) := fun i hi => hF i (Finset.mem_insert_of_mem hi)
      have hrestI : ∀ t : Finset ι, t ⊆ s → t.Nonempty → ∀ m : Nat,
          IsZero (integralSupportHomology (⋂ i ∈ t, F i) (m + d)) :=
        fun t ht htn m => hI t (ht.trans (Finset.subset_insert a s)) htn m
      have hG : ∀ i ∈ s, IsClosed (F a ∩ F i) :=
        fun i hi => (hF a (Finset.mem_insert_self a s)).inter (hrest i hi)
      have hGI : ∀ t : Finset ι, t ⊆ s → t.Nonempty → ∀ m : Nat,
          IsZero (integralSupportHomology (⋂ i ∈ t, F a ∩ F i) (m + d)) := by
        intro t ht htn m
        have h := hI (insert a t) (Finset.insert_subset_insert a ht)
          (Finset.insert_nonempty a t) m
        rw [Finset.set_biInter_insert] at h
        have he : (⋂ i ∈ t, F a ∩ F i) = F a ∩ ⋂ i ∈ t, F i :=
          Set.inter_biInter htn.to_set F (F a)
        rw [he]
        exact h
      have hoverlap : IsZero
          (integralSupportHomology (F a ∩ ⋃ i ∈ s, F i) ((n + d) + 1)) := by
        have h := ih (fun i => F a ∩ F i) hG hGI (n + 1)
        simpa only [Set.inter_iUnion, Nat.add_right_comm n 1 d] using h
      have ha₀ : IsZero (integralSupportHomology (F a) (n + d)) := by
        simpa using hI {a} (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self a s))
          (Finset.singleton_nonempty a) n
      rw [Finset.set_biUnion_insert]
      exact integralSupportHomology_union_isZero (F a) (⋃ i ∈ s, F i)
        (hF a (Finset.mem_insert_self a s)) (isClosed_biUnion_finset hrest) (n + d)
        hoverlap ha₀ (ih F hrest hrestI n)

theorem integralSupportHomology_finset_union_detected
    {ι : Type v} (s : Finset ι) (F : ι → Set X) (d : Nat)
    (hF : ∀ i ∈ s, IsClosed (F i))
    (hI : ∀ t : Finset ι, t ⊆ s → t.Nonempty → ∀ n : Nat,
      IsZero (integralSupportHomology (⋂ i ∈ t, F i) (n + (d + 1))))
    (hD : ∀ i ∈ s, ∀ a : integralSupportHomology (F i) d,
      (∀ x : X, ∀ hx : x ∈ F i,
        integralSupportHomologyRestriction (Set.singleton_subset_iff.mpr hx) d a = 0) →
      a = 0)
    (a : integralSupportHomology (⋃ i ∈ s, F i) d)
    (ha : ∀ x : X, ∀ hx : x ∈ ⋃ i ∈ s, F i,
      integralSupportHomologyRestriction (Set.singleton_subset_iff.mpr hx) d a = 0) :
    a = 0 := by
  classical
  induction s using Finset.induction_on generalizing F with
  | empty =>
      have h := integralSupportHomology_empty_isZero (X := X) d
      have h' : IsZero (integralSupportHomology (⋃ i ∈ (∅ : Finset ι), F i) d) := by
        simpa using h
      exact (ModuleCat.isZero_iff_subsingleton.mp h').elim _ _
  | @insert i s hi ih =>
      revert a
      rw [Finset.set_biUnion_insert]
      intro a ha
      have hrest : ∀ j ∈ s, IsClosed (F j) := fun j hj => hF j (Finset.mem_insert_of_mem hj)
      have hrestI : ∀ t : Finset ι, t ⊆ s → t.Nonempty → ∀ n : Nat,
          IsZero (integralSupportHomology (⋂ j ∈ t, F j) (n + (d + 1))) :=
        fun t ht htn n => hI t (ht.trans (Finset.subset_insert i s)) htn n
      have hG : ∀ j ∈ s, IsClosed (F i ∩ F j) :=
        fun j hj => (hF i (Finset.mem_insert_self i s)).inter (hrest j hj)
      have hGI : ∀ t : Finset ι, t ⊆ s → t.Nonempty → ∀ n : Nat,
          IsZero (integralSupportHomology (⋂ j ∈ t, F i ∩ F j) (n + (d + 1))) := by
        intro t ht htn n
        have h := hI (insert i t) (Finset.insert_subset_insert i ht)
          (Finset.insert_nonempty i t) n
        rw [Finset.set_biInter_insert] at h
        have he : (⋂ j ∈ t, F i ∩ F j) = F i ∩ ⋂ j ∈ t, F j :=
          Set.inter_biInter htn.to_set F (F i)
        rw [he]
        exact h
      have hoverlap : IsZero
          (integralSupportHomology (F i ∩ ⋃ j ∈ s, F j) (d + 1)) := by
        have h := integralSupportHomology_finset_union_isZero s
          (fun j => F i ∩ F j) (d + 1) hG hGI 0
        simpa only [Set.inter_iUnion, Nat.zero_add] using h
      apply integralSupportHomology_union_ext (F i) (⋃ j ∈ s, F j)
        (hF i (Finset.mem_insert_self i s)) (isClosed_biUnion_finset hrest) d hoverlap
      · rw [map_zero]
        apply hD i (Finset.mem_insert_self i s)
        intro x hx
        rw [← ConcreteCategory.comp_apply, integralSupportHomologyRestriction_comp]
        exact ha x (Set.mem_union_left _ hx)
      · rw [map_zero]
        apply ih F hrest hrestI (fun j hj => hD j (Finset.mem_insert_of_mem hj))
        intro x hx
        rw [← ConcreteCategory.comp_apply, integralSupportHomologyRestriction_comp]
        exact ha x (Set.mem_union_right _ hx)

end PoincareConjecture.Proofs.M02.Topology
