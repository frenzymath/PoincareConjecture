import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence

set_option autoImplicit false

open Set
open scoped Topology

namespace Poincare.Topology

variable {X I : Type*} [TopologicalSpace X]

theorem exists_exactly_two_closed_cover_members_of_two_sided_neighborhood
    (A : I → Set X) (hclosed : ∀ i, IsClosed (A i))
    (hregular : ∀ i, closure (interior (A i)) = A i)
    (hdisjoint : Pairwise (fun i j => Disjoint (interior (A i)) (interior (A j))))
    (hcover : (⋃ i, A i) = univ)
    {p : X} {K W U V : Set X} (hW : W ∈ 𝓝 p)
    (hpartition : W \ K = U ∪ V)
    (hU : IsPreconnected U) (hV : IsPreconnected V)
    (hneU : U.Nonempty) (hneV : V.Nonempty)
    (hpU : p ∈ closure U) (hpV : p ∈ closure V)
    (hdense : W ⊆ closure (U ∪ V))
    (hfront : ∀ i, W ∩ frontier (A i) ⊆ K)
    (hpfront : ∃ i, p ∈ frontier (A i)) :
    ∃ i j : I, i ≠ j ∧ U ⊆ interior (A i) ∧ V ⊆ interior (A j) ∧
      ∀ k, p ∈ A k ↔ k = i ∨ k = j := by
  have hpint (i : I) : p ∉ interior (A i) := by
    obtain ⟨k, hpk⟩ := hpfront
    by_cases hki : k = i
    · subst k
      exact hpk.2
    · have h := (hdisjoint hki).closure_left isOpen_interior
      rw [hregular k] at h
      exact disjoint_left.mp h ((hclosed k).closure_eq ▸ hpk.1)
  have hUV : U ∪ V ⊆ W \ K := hpartition.symm.subset
  have hside {S : Set X} (hS : IsPreconnected S) (hneS : S.Nonempty)
      (hSsub : S ⊆ U ∪ V) : ∃ i, S ⊆ interior (A i) := by
    obtain ⟨s, hs⟩ := hneS
    obtain ⟨i, hi⟩ := mem_iUnion.mp (show s ∈ ⋃ i, A i from hcover.symm ▸ mem_univ s)
    have havoid : Disjoint S (frontier (A i)) := by
      apply disjoint_left.mpr
      intro z hz hzfront
      exact (hUV (hSsub hz)).2 (hfront i ⟨(hUV (hSsub hz)).1, hzfront⟩)
    have hsint : s ∈ interior (A i) := by
      by_contra h
      exact disjoint_left.mp havoid hs ⟨subset_closure hi, h⟩
    exact ⟨i, preconnected_subset_interior_of_disjoint_frontier hS havoid ⟨s, hs, hsint⟩⟩
  obtain ⟨i, hi⟩ := hside hU hneU subset_union_left
  obtain ⟨j, hj⟩ := hside hV hneV subset_union_right
  have hpAi : p ∈ A i := (closure_minimal (hi.trans interior_subset) (hclosed i)) hpU
  have hpAj : p ∈ A j := (closure_minimal (hj.trans interior_subset) (hclosed j)) hpV
  have hij : i ≠ j := by
    intro heq
    have hsub : U ∪ V ⊆ A i := union_subset (hi.trans interior_subset)
      (heq ▸ hj.trans interior_subset)
    have hWA : W ⊆ A i := hdense.trans (closure_minimal hsub (hclosed i))
    exact hpint i (mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset hW hWA))
  refine ⟨i, j, hij, hi, hj, ?_⟩
  intro k
  constructor
  · intro hpk
    have hpclosure : p ∈ closure (interior (A k)) := (hregular k).symm ▸ hpk
    obtain ⟨z, hzW, hzA⟩ := mem_closure_iff.mp hpclosure
      (interior W) isOpen_interior (mem_interior_iff_mem_nhds.mpr hW)
    obtain ⟨q, hqA, hqUV⟩ := mem_closure_iff.mp (hdense (interior_subset hzW))
      (interior (A k)) isOpen_interior hzA
    rcases hqUV with hqU | hqV
    · exact Or.inl (by
        by_contra hki
        exact disjoint_left.mp (hdisjoint hki) hqA (hi hqU))
    · exact Or.inr (by
        by_contra hkj
        exact disjoint_left.mp (hdisjoint hkj) hqA (hj hqV))
  · rintro (rfl | rfl)
    · exact hpAi
    · exact hpAj

end Poincare.Topology
