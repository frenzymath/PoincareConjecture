import PoincareConjecture.Proofs.M76.Brown.LocallyFlatSeparation
import PoincareConjecture.Proofs.M76.Brown.ComplementaryRegionClosures
import PoincareConjecture.Proofs.M76.Mathlib.UnboundedComplementComponent

set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76.LocallyFlatTopologicalSphere

local notation "V3" => (Fin 3 → ℝ)

theorem exists_bounded_complement_components {S : Set V3}
    (hS : LocallyFlatTopologicalSphere S) :
    ∃ U V : Set V3, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = Sᶜ ∧ frontier U = S ∧ frontier V = S ∧
      Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧
      IsCompact (closure U) ∧ frontier (closure U) = S ∧
      ∀ x ∈ Sᶜ, connectedComponentIn Sᶜ x = U ∨ connectedComponentIn Sᶜ x = V := by
  let : CompactSpace (sphere (0 : V3) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : V3) 1)
  let : CompactSpace S := hS.parametrization.compactSpace
  have hcompact : IsCompact S := isCompact_iff_compactSpace.mpr inferInstance
  obtain ⟨U, V, hU, hV, hUc, hVc, hdis, hunion, hfrontU, hfrontV, hclass⟩ :=
    hS.exists_complement_components
  have hcompU (y : V3) (hy : y ∈ U) : connectedComponentIn Sᶜ y = U := by
    have hyout : y ∈ Sᶜ := hunion.subset (Or.inl hy)
    rcases hclass y hyout with h | h
    · exact h
    · exact False.elim (Set.disjoint_left.mp hdis hy (h.subset (mem_connectedComponentIn hyout)))
  have hcompV (y : V3) (hy : y ∈ V) : connectedComponentIn Sᶜ y = V := by
    have hyout : y ∈ Sᶜ := hunion.subset (Or.inr hy)
    rcases hclass y hyout with h | h
    · exact False.elim (Set.disjoint_left.mp hdis (h.subset (mem_connectedComponentIn hyout)) hy)
    · exact h
  have hneUV : U ≠ V := by
    intro heq
    obtain ⟨y, hy⟩ := hUc.nonempty
    exact Set.disjoint_left.mp hdis hy (heq.subset hy)
  have hdim : 1 < Module.rank ℝ V3 := Module.one_lt_rank_of_one_lt_finrank (by simp)
  obtain ⟨x, hx, hxunbounded, hother⟩ :=
    hcompact.isBounded.exists_unique_unbounded_complement_component hdim
  rcases hclass x hx with hxU | hxV
  · have hVbounded : Bornology.IsBounded V := by
      obtain ⟨y, hy⟩ := hVc.nonempty
      have hybounded := hother y (by rw [hcompV y hy, hxU]; exact hneUV.symm)
      rwa [hcompV y hy] at hybounded
    have hUunbounded : ¬ Bornology.IsBounded U := by rwa [hxU] at hxunbounded
    have hunion' : V ∪ U = Sᶜ := (union_comm V U).trans hunion
    exact ⟨V, U, hV, hU, hVc, hUc, hdis.symm, hunion', hfrontV, hfrontU,
      hVbounded, hUunbounded, hVbounded.isCompact_closure,
      BrownCollar.frontier_closure_region hV hdis.symm hunion' hfrontV hfrontU,
      fun y hy => (hclass y hy).symm⟩
  · have hUbounded : Bornology.IsBounded U := by
      obtain ⟨y, hy⟩ := hUc.nonempty
      have hybounded := hother y (by rw [hcompU y hy, hxV]; exact hneUV)
      rwa [hcompU y hy] at hybounded
    have hVunbounded : ¬ Bornology.IsBounded V := by rwa [hxV] at hxunbounded
    exact ⟨U, V, hU, hV, hUc, hVc, hdis, hunion, hfrontU, hfrontV,
      hUbounded, hVunbounded, hUbounded.isCompact_closure,
      BrownCollar.frontier_closure_region hU hdis hunion hfrontU hfrontV, hclass⟩

end PoincareConjecture.M76.LocallyFlatTopologicalSphere
