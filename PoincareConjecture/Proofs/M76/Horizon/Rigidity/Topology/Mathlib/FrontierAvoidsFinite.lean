import PoincareConjecture.Proofs.M76.Mathlib.PolygonRegionRecognition
import Mathlib.Analysis.Normed.Module.Connected











set_option autoImplicit false

open Set

namespace Poincare.Topology

theorem IsCompact.exists_frontier_not_mem_finite
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    {K V : Set E} (hK : IsCompact K) (hne : (interior K).Nonempty)
    (hV : V.Finite) (hdim : 1 < Module.rank ℝ E) :
    ∃ x ∈ frontier K, x ∉ V := by
  classical
  by_contra h
  have hfront : frontier K ⊆ V := by
    intro x hx
    by_contra hxV
    exact h ⟨x, hx, hxV⟩
  obtain ⟨x, hx⟩ := hne
  have hUinf : (interior K).Infinite :=
    infinite_of_mem_nhds x (isOpen_interior.mem_nhds hx)
  obtain ⟨y, hy, hyV⟩ := Set.not_subset.mp
    (show ¬ interior K ⊆ V from fun hsub => hUinf (hV.subset hsub))
  have hconn : IsConnected Vᶜ := hV.countable.isConnected_compl_of_one_lt_rank hdim
  have hdis : Disjoint (frontier (interior K)) Vᶜ :=
    Set.disjoint_left.mpr (fun _ hx hy => hy (hfront (frontier_interior_subset hx)))
  have hsub : Vᶜ ⊆ interior K := hconn.isPreconnected.m76_subset_of_disjoint_frontier
    isOpen_interior hdis ⟨y, hyV, hy⟩
  have hcover : K ∪ V = univ := by
    apply Set.eq_univ_of_forall
    intro z
    by_cases hz : z ∈ V
    · exact Or.inr hz
    · exact Or.inl (interior_subset (hsub hz))
  exact NoncompactSpace.noncompact_univ (hcover ▸ hK.union hV.isCompact)

end Poincare.Topology
