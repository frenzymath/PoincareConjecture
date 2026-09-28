import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set Topology

universe u v

variable {X : Type u} [TopologicalSpace X]

theorem IsPreconnected.disjoint_of_frontier_neighborhood
    {A V U : Set X} (hA : IsPreconnected A) (hAc : IsClosed A)
    (hV : IsOpen V) (hU : IsOpen U) (hfront : frontier V ⊆ U)
    (havoid : Disjoint (A ∩ V) U) (hout : (A \ V).Nonempty) :
    Disjoint A V := by
  have hclosed : IsClosed (A ∩ V) := by
    apply isClosed_of_closure_subset
    intro x hx
    have hxA : x ∈ A := hAc.closure_subset (closure_mono inter_subset_left hx)
    have hxcl : x ∈ closure V := closure_mono inter_subset_right hx
    have hxUc : x ∈ Uᶜ :=
      closure_minimal (Set.disjoint_left.mp havoid) hU.isClosed_compl hx
    refine ⟨hxA, ?_⟩
    by_contra hxV
    exact hxUc (hfront ⟨hxcl, by simpa only [hV.interior_eq] using hxV⟩)
  have hcover : A ⊆ (A ∩ V) ∪ Vᶜ := by
    intro x hx
    by_cases hxV : x ∈ V
    · exact Or.inl ⟨hx, hxV⟩
    · exact Or.inr hxV
  have hdisj : Disjoint (A ∩ V) Vᶜ :=
    disjoint_compl_right.mono_left inter_subset_right
  rcases (isPreconnected_iff_subset_of_fully_disjoint_closed hAc).mp hA
    (A ∩ V) Vᶜ hclosed hV.isClosed_compl hcover hdisj with hin | houtside
  · obtain ⟨x, hxA, hxV⟩ := hout
    exact (hxV (hin hxA).2).elim
  · exact Set.disjoint_left.mpr (fun _ hxA hxV => houtside hxA hxV)

theorem IsPreconnected.subset_of_disjoint_frontier
    {A V : Set X} (hA : IsPreconnected A) (hV : IsOpen V)
    (hfront : Disjoint A (frontier V)) (hmeet : (A ∩ V).Nonempty) : A ⊆ V := by
  have hcover : A ⊆ closure V ∪ Vᶜ := by
    intro x _
    by_cases hx : x ∈ V
    · exact Or.inl (subset_closure hx)
    · exact Or.inr hx
  have hdisj : A ∩ (closure V ∩ Vᶜ) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hxA, hxcl, hxV⟩
    exact Set.disjoint_left.mp hfront hxA
      ⟨hxcl, by simpa only [hV.interior_eq, mem_compl_iff] using hxV⟩
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hA
    (closure V) Vᶜ isClosed_closure hV.isClosed_compl hcover hdisj with hin | hout
  · intro x hx
    by_contra hxV
    exact Set.disjoint_left.mp hfront hx
      ⟨hin hx, by simpa only [hV.interior_eq] using hxV⟩
  · obtain ⟨x, hxA, hxV⟩ := hmeet
    exact (hout hxA hxV).elim

theorem pairwise_disjoint_of_frontier_subset_root
    {ι : Type v} {A : Set X} (V : ι → Set X)
    (hV : ∀ i, IsOpen (V i)) (hconn : ∀ i, IsPreconnected (V i))
    (hroot : ∀ i, Disjoint (V i) A)
    (hfront : ∀ i, frontier (V i) ⊆ A)
    (hne : ∀ i, (frontier (V i)).Nonempty)
    (hdisj : Pairwise (fun i j => Disjoint (frontier (V i)) (frontier (V j)))) :
    Pairwise (fun i j => Disjoint (V i) (V j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hijsub : V i ⊆ V j :=
    (hconn i).subset_of_disjoint_frontier (hV j)
      ((hroot i).mono_right (hfront j)) ⟨x, hxi, hxj⟩
  have hjisub : V j ⊆ V i :=
    (hconn j).subset_of_disjoint_frontier (hV i)
      ((hroot j).mono_right (hfront i)) ⟨x, hxj, hxi⟩
  have heq := subset_antisymm hijsub hjisub
  obtain ⟨z, hz⟩ := hne i
  exact Set.disjoint_left.mp (hdisj hij) hz (heq ▸ hz)

theorem root_union_outward_eq_univ [PreconnectedSpace X]
    {ι : Type v} [Finite ι] {A : Set X} (hA : IsClosed A) (hne : A.Nonempty)
    (V : ι → Set X) (hV : ∀ i, IsOpen (V i))
    (hfront : ∀ i, frontier (V i) ⊆ A)
    (hcollar : ∀ x ∈ frontier A, ∃ i, A ∪ V i ∈ 𝓝 x) :
    A ∪ ⋃ i, V i = univ := by
  let B := A ∪ ⋃ i, V i
  have hclosed : IsClosed B := by
    have heq : B = A ∪ ⋃ i, closure (V i) := by
      apply subset_antisymm
      · exact union_subset_union_right _ (iUnion_mono (fun _ => subset_closure))
      · rintro x (hx | hx)
        · exact Or.inl hx
        · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
          rw [closure_eq_self_union_frontier] at hi
          exact hi.elim (fun hv => Or.inr (mem_iUnion.mpr ⟨i, hv⟩))
            (fun hf => Or.inl (hfront i hf))
    rw [heq]
    exact hA.union (isClosed_iUnion_of_finite (fun _ => isClosed_closure))
  have hopen : IsOpen B := by
    apply isOpen_iff_mem_nhds.mpr
    rintro x (hx | hx)
    · by_cases hi : x ∈ interior A
      · exact Filter.mem_of_superset (isOpen_interior.mem_nhds hi)
          (fun _ hz => Or.inl (interior_subset hz))
      · have hf : x ∈ frontier A := ⟨subset_closure hx, hi⟩
        obtain ⟨i, hni⟩ := hcollar x hf
        exact Filter.mem_of_superset hni
          (union_subset_union_right _ (subset_iUnion V i))
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact Filter.mem_of_superset ((hV i).mem_nhds hi)
        (fun _ hz => Or.inr (mem_iUnion.mpr ⟨i, hz⟩))
  exact IsClopen.eq_univ ⟨hclosed, hopen⟩ (hne.mono subset_union_left)
