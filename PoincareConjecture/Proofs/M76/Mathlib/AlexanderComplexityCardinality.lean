import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Separation.Basic
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

open Set

namespace Set

variable {X ι κ : Type*} [TopologicalSpace X]

theorem exists_member_of_connected_punctured_cover [Finite κ]
    (F : κ → Set X) (hF : ∀ j, IsClosed (F j)) (q : X)
    (hpair : Pairwise (fun i j => F i ∩ F j ⊆ {q}))
    {C : Set X} (hC : IsConnected C) (hcover : C ⊆ ⋃ j, F j \ {q}) :
    ∃ j, C ⊆ F j \ {q} := by
  classical
  obtain ⟨x, hxC⟩ := hC.nonempty
  obtain ⟨j, hxj⟩ := mem_iUnion.mp (hcover hxC)
  let R : Set X := ⋃ k : {k : κ // k ≠ j}, F k
  have hR : IsClosed R := isClosed_iUnion_of_finite (fun k => hF k)
  have hcommon : F j ∩ R ⊆ {q} := by
    intro y hy
    obtain ⟨k, hyk⟩ := mem_iUnion.mp hy.2
    exact hpair (Ne.symm k.property) ⟨hy.1, hyk⟩
  have havoid : ∀ y ∈ C, y ∉ ({q} : Set X) := by
    intro y hy
    obtain ⟨k, hyk⟩ := mem_iUnion.mp (hcover hy)
    exact hyk.2
  have hcover' : C ⊆ F j ∪ R := by
    intro y hy
    obtain ⟨k, hyk⟩ := mem_iUnion.mp (hcover hy)
    by_cases hkj : k = j
    · exact Or.inl (hkj ▸ hyk.1)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨k, hkj⟩, hyk.1⟩)
  have hinter : C ∩ (F j ∩ R) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    exact fun y hy => havoid y hy.1 (hcommon hy.2)
  have hside := isPreconnected_iff_subset_of_disjoint_closed.mp hC.isPreconnected
    (F j) R (hF j) hR hcover' hinter
  have hleft : C ⊆ F j := hside.resolve_right
    (fun h => hxj.2 (hcommon ⟨hxj.1, h hxC⟩))
  exact ⟨j, fun y hy => ⟨hleft hy, havoid y hy⟩⟩

theorem exists_equiv_punctured_closed_connected_families [Finite ι] [Finite κ]
    (D : ι → Set X) (F : κ → Set X) (hD : ∀ i, IsClosed (D i))
    (hF : ∀ j, IsClosed (F j)) (q : X)
    (hcD : ∀ i, IsConnected (D i \ {q})) (hcF : ∀ j, IsConnected (F j \ {q}))
    (hpD : Pairwise (fun i j => D i ∩ D j ⊆ {q}))
    (hpF : Pairwise (fun i j => F i ∩ F j ⊆ {q}))
    (hcover : (⋃ i, D i \ {q}) = ⋃ j, F j \ {q}) :
    ∃ e : ι ≃ κ, ∀ i, D i \ {q} = F (e i) \ {q} := by
  classical
  have hexD (i : ι) : ∃ j, D i \ {q} ⊆ F j \ {q} :=
    exists_member_of_connected_punctured_cover F hF q hpF (hcD i)
      (fun _ hx => hcover ▸ mem_iUnion.mpr ⟨i, hx⟩)
  have hexF (j : κ) : ∃ i, F j \ {q} ⊆ D i \ {q} :=
    exists_member_of_connected_punctured_cover D hD q hpD (hcF j)
      (fun _ hx => hcover.symm ▸ mem_iUnion.mpr ⟨j, hx⟩)
  choose f hf using hexD
  choose g hg using hexF
  have hgf (i : ι) : g (f i) = i := by
    obtain ⟨x, hx⟩ := (hcD i).nonempty
    by_contra hne
    exact hx.2 (hpD hne ⟨(hg (f i) (hf i hx)).1, hx.1⟩)
  have hfg (j : κ) : f (g j) = j := by
    obtain ⟨x, hx⟩ := (hcF j).nonempty
    by_contra hne
    exact hx.2 (hpF hne ⟨(hf (g j) (hg j hx)).1, hx.1⟩)
  let e : ι ≃ κ := ⟨f, g, hgf, hfg⟩
  refine ⟨e, fun i => Subset.antisymm (hf i) ?_⟩
  intro x hx
  have h := hg (f i) hx
  rwa [hgf i] at h

theorem IsPreconnected.closure_sdiff_singleton_eq [T1Space X] {s : Set X}
    (hs : IsPreconnected s) (hclosed : IsClosed s) (q : X)
    (hne : (s \ {q}).Nonempty) : closure (s \ {q}) = s := by
  refine Subset.antisymm (closure_minimal sdiff_subset hclosed) ?_
  by_cases hq : q ∈ closure (s \ {q})
  · intro x hx
    by_cases hxq : x = q
    · exact hxq.symm ▸ hq
    · exact subset_closure ⟨hx, hxq⟩
  · have hcover : s ⊆ {q} ∪ closure (s \ {q}) := by
      intro x hx
      by_cases hxq : x = q
      · exact Or.inl hxq
      · exact Or.inr (subset_closure ⟨hx, hxq⟩)
    have hinter : s ∩ ({q} ∩ closure (s \ {q})) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hq ((show x = q from hx.2.1) ▸ hx.2.2)
    have hside := isPreconnected_iff_subset_of_disjoint_closed.mp hs
      {q} (closure (s \ {q})) isClosed_singleton isClosed_closure hcover hinter
    exact hside.resolve_left (fun h => by
      obtain ⟨x, hx⟩ := hne
      exact hx.2 (h hx.1))

end Set
