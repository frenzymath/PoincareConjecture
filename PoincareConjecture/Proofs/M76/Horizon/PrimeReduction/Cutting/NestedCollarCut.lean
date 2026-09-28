import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.CollarCutCarrier
import PoincareConjecture.Proofs.M76.PrimeReduction.PLDomainIntersection

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.nested_collar_cut
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {R P U : Set X}
    (he : PLDomain e R) (hR : IsCompact R) (hP : IsCompact P)
    (hRP : R ⊆ interior P) (hU : IsOpen U) (hUR : closure U ⊆ interior R)
    (hcut : PLDomain e (P \ U)) :
    PLDomain e (R \ U) ∧ IsCompact (R \ U) ∧
      R \ U = R ∩ (P \ U) ∧
      frontier (R \ U) = frontier R ∪ frontier U ∧
      frontier (P \ U) = frontier P ∪ frontier U ∧
      Disjoint (R \ U) (frontier P) ∧ frontier R ⊆ R \ U ∧
      frontier U ⊆ interior R ∧
      (P \ U) \ (R \ U) = P \ R := by
  have hUP : closure U ⊆ interior P := hUR.trans interior_subset |>.trans hRP
  obtain ⟨hQc, _, hQf, _, _, _⟩ :=
    compact_collar_cut_geometry hR hU hUR
  obtain ⟨_, _, hPf, _, _, _⟩ := compact_collar_cut_geometry hP hU hUP
  have hEq : R \ U = R ∩ (P \ U) := by
    ext x
    constructor
    · exact fun h => ⟨h.1, interior_subset (hRP h.1), h.2⟩
    · exact fun h => ⟨h.1, h.2.2⟩
  have hfrontDis : Disjoint (frontier R) (frontier (P \ U)) := by
    rw [hPf]
    apply disjoint_left.mpr
    intro x hx hy
    rcases hy with hy | hy
    · exact hy.2 (hRP (hR.isClosed.frontier_subset hx))
    · exact hx.2 (hUR (frontier_subset_closure hy))
  refine ⟨hEq.symm ▸ he.inter_of_disjoint_frontiers hcut hfrontDis,
    hQc, hEq, hQf, hPf, ?_, ?_, frontier_subset_closure.trans hUR, ?_⟩
  · exact disjoint_left.mpr (fun _ hx hy => hy.2 (hRP hx.1))
  · exact fun x hx => ⟨hR.isClosed.frontier_subset hx,
      fun hxU => hx.2 (hUR (subset_closure hxU))⟩
  · ext x
    constructor
    · intro hx
      exact ⟨hx.1.1, fun hxR => hx.2 ⟨hxR, hx.1.2⟩⟩
    · intro hx
      have hxU : x ∉ U := fun hxU => hx.2 (interior_subset (hUR (subset_closure hxU)))
      exact ⟨⟨hx.1, hxU⟩, fun hxR => hx.2 hxR.1⟩

end PoincareConjecture.M76
