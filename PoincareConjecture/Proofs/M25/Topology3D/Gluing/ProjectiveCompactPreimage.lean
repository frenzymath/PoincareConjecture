import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ProjectiveCover












set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M25.Topology3D.StandardPuncturedProjectiveCover




theorem compact_preimage_topology
    {Q : Type u} [TopologicalSpace Q]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q]
    {p : RealProjectiveThree} {U : Set Q}
    (C : PoincareConjecture.StandardPuncturedProjectiveCover Q p U)
    {K : Set Q} (hK : IsCompact K) (hKU : K ⊆ U) :
    let L := projectiveCoverDomain p ∩ C.cover ⁻¹' K
    IsCompact L ∧
      interior L = projectiveCoverDomain p ∩ C.cover ⁻¹' interior K ∧
      frontier L = projectiveCoverDomain p ∩ C.cover ⁻¹' frontier K ∧
      (fun x : UnitThreeSphere => -x) '' L = L := by
  classical
  let L : Set UnitThreeSphere := projectiveCoverDomain p ∩ C.cover ⁻¹' K
  change IsCompact L ∧
    interior L = projectiveCoverDomain p ∩ C.cover ⁻¹' interior K ∧
    frontier L = projectiveCoverDomain p ∩ C.cover ⁻¹' frontier K ∧
    (fun x : UnitThreeSphere => -x) '' L = L
  let i : projectiveCoverDomain p → UnitThreeSphere := Subtype.val
  let j : U → Q := Subtype.val
  let f : projectiveCoverDomain p → Q := fun x => C.cover x.1
  have hiContinuous : Continuous i := continuous_subtype_val
  have hiOpen : IsOpenMap i :=
    (isOpen_projectiveCoverDomain p).isOpenMap_subtype_val
  have hjInducing : IsInducing j := IsInducing.subtypeVal
  have hcompactTarget : IsCompact (j ⁻¹' K) := by
    apply hjInducing.isCompact_preimage' hK
    intro y hy
    exact ⟨⟨y, hKU hy⟩, rfl⟩
  have hcompactRestricted :
      IsCompact (restrictedCover C ⁻¹' (j ⁻¹' K)) :=
    (restrictedCover_isProperMap C).isCompact_preimage hcompactTarget
  have himage : i '' (restrictedCover C ⁻¹' (j ⁻¹' K)) = L := by
    ext x
    change (∃ y : projectiveCoverDomain p, C.cover y.1 ∈ K ∧ y.1 = x) ↔
      x ∈ projectiveCoverDomain p ∧ C.cover x ∈ K
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, hKx⟩
      exact ⟨⟨x, hx⟩, hKx, rfl⟩
  have hcompact : IsCompact L := by
    rw [← himage]
    exact hcompactRestricted.image hiContinuous
  have hclosed : IsClosed L := hcompact.isClosed
  have hlocal : IsLocalHomeomorph f := isLocalHomeomorph_domainRestrict C
  have hpreimage : i ⁻¹' L = f ⁻¹' K := by
    ext x
    change (x.1 ∈ projectiveCoverDomain p ∧ C.cover x.1 ∈ K) ↔
      C.cover x.1 ∈ K
    exact ⟨fun hx => hx.2, fun hx => ⟨x.2, hx⟩⟩
  have hinteriorPullback : i ⁻¹' interior L = f ⁻¹' interior K := by
    rw [hiOpen.preimage_interior_eq_interior_preimage hiContinuous,
      hpreimage,
      ← hlocal.isOpenMap.preimage_interior_eq_interior_preimage hlocal.continuous]
  have hfrontierPullback : i ⁻¹' frontier L = f ⁻¹' frontier K := by
    rw [hiOpen.preimage_frontier_eq_frontier_preimage hiContinuous,
      hpreimage,
      ← hlocal.isOpenMap.preimage_frontier_eq_frontier_preimage hlocal.continuous]
  have hinterior :
      interior L = projectiveCoverDomain p ∩ C.cover ⁻¹' interior K := by
    apply Subset.antisymm
    · intro x hx
      have hxL : x ∈ L := interior_subset hx
      have hxD : x ∈ projectiveCoverDomain p := hxL.1
      refine ⟨hxD, ?_⟩
      have hx' : (⟨x, hxD⟩ : projectiveCoverDomain p) ∈ i ⁻¹' interior L := hx
      rw [hinteriorPullback] at hx'
      exact hx'
    · rintro x ⟨hxD, hx⟩
      have hx' : (⟨x, hxD⟩ : projectiveCoverDomain p) ∈ f ⁻¹' interior K := hx
      rw [← hinteriorPullback] at hx'
      exact hx'
  have hfrontier :
      frontier L = projectiveCoverDomain p ∩ C.cover ⁻¹' frontier K := by
    apply Subset.antisymm
    · intro x hx
      have hxL : x ∈ closure L := frontier_subset_closure hx
      rw [hclosed.closure_eq] at hxL
      have hxD : x ∈ projectiveCoverDomain p := hxL.1
      refine ⟨hxD, ?_⟩
      have hx' : (⟨x, hxD⟩ : projectiveCoverDomain p) ∈ i ⁻¹' frontier L := hx
      rw [hfrontierPullback] at hx'
      exact hx'
    · rintro x ⟨hxD, hx⟩
      have hx' : (⟨x, hxD⟩ : projectiveCoverDomain p) ∈ f ⁻¹' frontier K := hx
      rw [← hfrontierPullback] at hx'
      exact hx'
  have hneg : ∀ x ∈ L, (-x : UnitThreeSphere) ∈ L := by
    intro x hx
    refine ⟨(neg_mem_projectiveCoverDomain_iff p x).mpr hx.1, ?_⟩
    change C.cover (-x) ∈ K
    rw [cover_neg C hx.1]
    exact hx.2
  have hantipode : (fun x : UnitThreeSphere => -x) '' L = L := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hneg x hx
    · intro x hx
      refine ⟨-x, hneg x hx, ?_⟩
      simp only [neg_neg]
  exact ⟨hcompact, hinterior, hfrontier, hantipode⟩

end PoincareConjecture.M25.Topology3D.StandardPuncturedProjectiveCover
