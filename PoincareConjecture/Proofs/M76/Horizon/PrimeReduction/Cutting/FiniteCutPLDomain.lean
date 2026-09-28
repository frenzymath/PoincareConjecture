import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.FiniteCollarCuts
import PoincareConjecture.Proofs.M76.Wall.ProtectedPLIntersection










set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.sdiff_iUnion_of_disjoint_collar_closures
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} {U : κ → Set X}
    (he : PLDomain e R) (hR : IsCompact R)
    (hU : ∀ i, IsOpen (U i)) (hinside : ∀ i, closure (U i) ⊆ interior R)
    (hdis : Pairwise fun i j => Disjoint (closure (U i)) (closure (U j)))
    (hcut : ∀ i, PLDomain e (R \ U i)) :
    PLDomain e (R \ ⋃ i, U i) := by
  classical
  obtain ⟨hQ, _, hQfront, _⟩ := finite_collar_cut_geometry hR hU hinside hdis
  refine ⟨he.cover, he.compatible, hQ.isClosed, ?_⟩
  intro x hx
  rw [hQfront] at hx
  rcases hx with hxR | hxnew
  · let O := (⋃ i, closure (U i))ᶜ
    have hO : IsOpen O := (isClosed_iUnion_of_finite fun i => isClosed_closure).isOpen_compl
    have hxO : x ∈ O := by
      intro hxC
      obtain ⟨i, hxi⟩ := mem_iUnion.mp hxC
      exact hxR.2 (hinside i hxi)
    obtain ⟨ell, v, H, hv, hxH, hzero, hcompat, hhalf⟩ := he.halfspace x hxR
    let B := H.restrOpen O hO
    refine ⟨ell, v, B, hv, ⟨hxH, hxO⟩, hzero, ?_, ?_⟩
    · intro i
      exact (e i).piecewiseAffine_compatible_restrOpen_right H (hcompat i) hO
    · intro y hy
      change y ∈ R \ ⋃ i, U i ↔ 0 ≤ ell (H y)
      constructor
      · exact fun h => (hhalf y hy.1).mp h.1
      · intro h
        refine ⟨(hhalf y hy.1).mpr h, ?_⟩
        intro hyU
        obtain ⟨i, hyi⟩ := mem_iUnion.mp hyU
        exact hy.2 (mem_iUnion.mpr ⟨i, subset_closure hyi⟩)
  · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxnew
    have hxsingle : x ∈ frontier (R \ U i) := by
      rw [(compact_collar_cut_geometry hR (hU i) (hinside i)).2.2.1]
      exact Or.inr hxi
    let O := (⋃ j : {j : κ // j ≠ i}, closure (U j.val))ᶜ
    have hO : IsOpen O :=
      (isClosed_iUnion_of_finite fun j : {j : κ // j ≠ i} =>
        isClosed_closure (s := U j.val)).isOpen_compl
    have hxO : x ∈ O := by
      intro hxC
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hxC
      exact disjoint_left.mp (hdis (Ne.symm j.property))
        (frontier_subset_closure hxi) hxj
    obtain ⟨ell, v, H, hv, hxH, hzero, hcompat, hhalf⟩ := (hcut i).halfspace x hxsingle
    let B := H.restrOpen O hO
    refine ⟨ell, v, B, hv, ⟨hxH, hxO⟩, hzero, ?_, ?_⟩
    · intro j
      exact (e j).piecewiseAffine_compatible_restrOpen_right H (hcompat j) hO
    · intro y hy
      change y ∈ R \ ⋃ j, U j ↔ 0 ≤ ell (H y)
      constructor
      · intro h
        apply (hhalf y hy.1).mp
        exact ⟨h.1, fun hyi => h.2 (mem_iUnion.mpr ⟨i, hyi⟩)⟩
      · intro h
        obtain ⟨hyR, hyi⟩ := (hhalf y hy.1).mpr h
        refine ⟨hyR, ?_⟩
        intro hyU
        obtain ⟨j, hyj⟩ := mem_iUnion.mp hyU
        by_cases hji : j = i
        · exact hyi (hji ▸ hyj)
        · exact hy.2 (mem_iUnion.mpr ⟨⟨j, hji⟩, subset_closure hyj⟩)

end PoincareConjecture.M76
