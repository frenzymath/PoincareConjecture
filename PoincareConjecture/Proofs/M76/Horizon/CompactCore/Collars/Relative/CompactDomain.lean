import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Domains.CompactSubdomain
import PoincareConjecture.Proofs.M76.Wall.ProtectedPLIntersection

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem PLDomain.exists_compact_relative_frontier_domain_with_agreement
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {D W : Set X}
    (hD : IsCompact D) (heW : PLDomain e W)
    (hcross : ∀ x ∈ frontier D ∩ frontier W,
      ∃ B : OpenPartialHomeomorph X V3,
        x ∈ B.source ∧ B x = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ B.source, y ∈ frontier D ↔ B y 0 = 0) ∧
        ∀ y ∈ B.source, y ∈ frontier W ↔ B y 1 = 0) :
    ∃ K V : Set X, IsCompact K ∧ PLDomain e K ∧ K ⊆ W ∧
      IsOpen V ∧ frontier D ∩ W ⊆ V ∧
      K ∩ V = W ∩ V ∧
      (∀ x ∈ V, x ∈ frontier K ↔ x ∈ frontier W) ∧
      frontier D ∩ K = frontier D ∩ W ∧
      frontier D ∩ frontier K = frontier D ∩ frontier W ∧
      ∀ x ∈ frontier D ∩ frontier K,
        ∃ B : OpenPartialHomeomorph X V3,
          x ∈ B.source ∧ B x = 0 ∧
          (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
          (∀ y ∈ B.source, y ∈ frontier D ↔ B y 0 = 0) ∧
          ∀ y ∈ B.source, y ∈ frontier K ↔ B y 1 = 0 := by
  let S := frontier D ∩ W
  have hS : IsCompact S :=
    (hD.of_isClosed_subset isClosed_frontier hD.isClosed.frontier_subset).inter_right heW.closed
  obtain ⟨K, V, hK, heK, hSK, hKW, hV, hSV, _, hKV, hfront, _⟩ :=
    heW.exists_compact_subdomain_near hS inter_subset_right isOpen_univ (subset_univ _)
  have hKW' : K ⊆ W := hKW.trans inter_subset_left
  have hsurface : frontier D ∩ K = S := by
    apply Subset.antisymm
    · exact fun x hx => ⟨hx.1, hKW' hx.2⟩
    · exact fun x hx => ⟨hx.1, hSK hx⟩
  have hfrontV (x : X) (hx : x ∈ V) : x ∈ frontier K ↔ x ∈ frontier W := by
    constructor
    · exact fun h => (hfront.subset ⟨h, hx⟩).1
    · exact fun h => (hfront.symm.subset ⟨h, hx⟩).1
  have hseam : frontier D ∩ frontier K = frontier D ∩ frontier W := by
    apply Subset.antisymm
    · intro x hx
      have hxS : x ∈ S := ⟨hx.1, hKW' (heK.closed.frontier_subset hx.2)⟩
      exact ⟨hx.1, (hfrontV x (hSV hxS)).mp hx.2⟩
    · intro x hx
      have hxS : x ∈ S := ⟨hx.1, heW.closed.frontier_subset hx.2⟩
      exact ⟨hx.1, (hfrontV x (hSV hxS)).mpr hx.2⟩
  refine ⟨K, V, hK, heK, hKW', hV, hSV, hKV, hfrontV, hsurface, hseam, ?_⟩
  intro x hx
  have hx' := hseam.subset hx
  have hxV := hSV (show x ∈ S from ⟨hx'.1, heW.closed.frontier_subset hx'.2⟩)
  obtain ⟨B, hxB, hBx, hcompat, hDchart, hWchart⟩ := hcross x hx'
  refine ⟨B.restrOpen V hV, ⟨hxB, hxV⟩, hBx, ?_, ?_, ?_⟩
  · intro i
    exact (e i).piecewiseAffine_compatible_restrOpen_right B (hcompat i) hV
  · intro y hy
    exact hDchart y hy.1
  · intro y hy
    exact (hfrontV y hy.2).trans (hWchart y hy.1)

theorem PLDomain.exists_compact_relative_frontier_domain_with_neighborhood
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {D W : Set X}
    (hD : IsCompact D) (heW : PLDomain e W)
    (hcross : ∀ x ∈ frontier D ∩ frontier W,
      ∃ B : OpenPartialHomeomorph X V3,
        x ∈ B.source ∧ B x = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ B.source, y ∈ frontier D ↔ B y 0 = 0) ∧
        ∀ y ∈ B.source, y ∈ frontier W ↔ B y 1 = 0) :
    ∃ K V : Set X, IsCompact K ∧ PLDomain e K ∧ K ⊆ W ∧
      IsOpen V ∧ frontier D ∩ W ⊆ V ∧
      (∀ x ∈ V, x ∈ frontier K ↔ x ∈ frontier W) ∧
      frontier D ∩ K = frontier D ∩ W ∧
      frontier D ∩ frontier K = frontier D ∩ frontier W ∧
      ∀ x ∈ frontier D ∩ frontier K,
        ∃ B : OpenPartialHomeomorph X V3,
          x ∈ B.source ∧ B x = 0 ∧
          (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
          (∀ y ∈ B.source, y ∈ frontier D ↔ B y 0 = 0) ∧
          ∀ y ∈ B.source, y ∈ frontier K ↔ B y 1 = 0 := by
  obtain ⟨K, V, hK, heK, hKW, hV, hSV, _, hfront, hsurface, hseam, hcrossK⟩ :=
    heW.exists_compact_relative_frontier_domain_with_agreement hD hcross
  exact ⟨K, V, hK, heK, hKW, hV, hSV, hfront, hsurface, hseam, hcrossK⟩

theorem PLDomain.exists_compact_relative_frontier_domain
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {D W : Set X}
    (hD : IsCompact D) (heW : PLDomain e W)
    (hcross : ∀ x ∈ frontier D ∩ frontier W,
      ∃ B : OpenPartialHomeomorph X V3,
        x ∈ B.source ∧ B x = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ B.source, y ∈ frontier D ↔ B y 0 = 0) ∧
        ∀ y ∈ B.source, y ∈ frontier W ↔ B y 1 = 0) :
    ∃ K : Set X, IsCompact K ∧ PLDomain e K ∧ K ⊆ W ∧
      frontier D ∩ K = frontier D ∩ W ∧
      frontier D ∩ frontier K = frontier D ∩ frontier W ∧
      ∀ x ∈ frontier D ∩ frontier K,
        ∃ B : OpenPartialHomeomorph X V3,
          x ∈ B.source ∧ B x = 0 ∧
          (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid V3) ∧
          (∀ y ∈ B.source, y ∈ frontier D ↔ B y 0 = 0) ∧
          ∀ y ∈ B.source, y ∈ frontier K ↔ B y 1 = 0 := by
  obtain ⟨K, _, hK, heK, hKW, _, _, _, hsurface, hseam, hcrossK⟩ :=
    heW.exists_compact_relative_frontier_domain_with_neighborhood hD hcross
  exact ⟨K, hK, heK, hKW, hsurface, hseam, hcrossK⟩

end PoincareConjecture.M76
