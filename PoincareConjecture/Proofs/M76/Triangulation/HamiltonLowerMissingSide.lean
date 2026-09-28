import PoincareConjecture.Proofs.M76.Triangulation.HamiltonWallComplementBall










set_option autoImplicit false

open Set Metric

namespace PoincareConjecture.M76

variable {X α : Type*} [TopologicalSpace X] [T2Space X]
  {U : TopologicalSpace.Opens X} {H : Set X}
  {e : α → OpenPartialHomeomorph U (Fin 3 → ℝ)} {K S : Set U}

local notation "R" => ((Subtype.val : U → X) ⁻¹' H)





theorem PLDomain.relative_wall_missing_side [Nonempty U]
    (hH : IsCompact H) (hHU : frontier H ⊆ (U : Set X))
    (hK : IsCompact K) (hKD : PLDomain e K)
    (hS : S ⊆ interior R) (hfront : frontier K = frontier R ∪ S)
    (hretain : (Subtype.val : R → U) ⁻¹' frontier R ⊆
      interior ((Subtype.val : R → U) ⁻¹' K)) :
    let D := H \ ((Subtype.val : U → X) '' ((Subtype.val : R → U) ''
      interior ((Subtype.val : R → U) ⁻¹' K)))
    IsCompact D ∧ D ⊆ interior H ∧ frontier D = (Subtype.val : U → X) '' S ∧
      ∀ y : U, y ∈ interior R → ((y : X) ∈ D ↔ y ∉ interior K) := by
  classical
  let D := H \ ((Subtype.val : U → X) '' ((Subtype.val : R → U) ''
    interior ((Subtype.val : R → U) ⁻¹' K)))
  let Kr : Set R := (Subtype.val : R → U) ⁻¹' K
  let B : Set X := (Subtype.val : U → X) '' K
  let j : R → H := fun z => ⟨((z : U) : X), z.property⟩
  have hj : Topology.IsEmbedding j :=
    (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal).codRestrict
      H (fun z => z.property)
  have hjrange : range j = (Subtype.val : H → X) ⁻¹' (U : Set X) := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact (z : U).property
    · intro hx
      exact ⟨⟨⟨x, hx⟩, x.property⟩, rfl⟩
  have hjopen : IsOpenMap j := by
    apply Topology.IsOpenEmbedding.isOpenMap
    refine ⟨hj, ?_⟩
    rw [hjrange]
    exact U.isOpen.preimage continuous_subtype_val
  have hDimage : D = (Subtype.val : H → X) '' (j '' interior Kr)ᶜ := by
    ext x
    constructor
    · intro hx
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      rintro ⟨z, hz, heq⟩
      exact hx.2 ⟨z, ⟨z, hz, rfl⟩, congrArg Subtype.val heq⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x.property, ?_⟩
      rintro ⟨y, ⟨z, hz, hzy⟩, hyx⟩
      exact hx ⟨z, hz, Subtype.ext ((congrArg Subtype.val hzy).trans hyx)⟩
  have hDcompact : IsCompact D := by
    let : CompactSpace H := isCompact_iff_compactSpace.mp hH
    rw [hDimage]
    exact (hjopen _ isOpen_interior).isClosed_compl.isCompact.image continuous_subtype_val
  have hfrontR : frontier R = (Subtype.val : U → X) ⁻¹' frontier H :=
    (U.isOpen.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage
      (continuous_subtype_val : Continuous (Subtype.val : U → X)) H).symm
  have hDint : D ⊆ interior H := by
    intro x hx
    by_contra hxi
    have hxf : x ∈ frontier H := ⟨hH.isClosed.closure_eq.symm ▸ hx.1, hxi⟩
    let y : U := ⟨x, hHU hxf⟩
    have hyR : y ∈ R := hx.1
    have hyf : y ∈ frontier R := hfrontR.symm ▸ hxf
    have hyK : (⟨y, hyR⟩ : R) ∈ interior Kr := hretain hyf
    exact hx.2 ⟨y, ⟨⟨y, hyR⟩, hyK, rfl⟩, rfl⟩
  have hDlocal (y : U) (hy : y ∈ interior R) :
      (y : X) ∈ D ↔ y ∉ interior K := by
    let z : R := ⟨y, interior_subset hy⟩
    have hmem : (y : X) ∈ D ↔ z ∉ interior Kr := by
      constructor
      · intro hx hz
        exact hx.2 ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      · intro hz
        refine ⟨z.property, ?_⟩
        rintro ⟨w, ⟨v, hv, hvw⟩, hwy⟩
        have hvz : v = z := Subtype.ext
          (Subtype.ext ((congrArg Subtype.val hvw).trans hwy))
        exact hz (hvz ▸ hv)
    have hint : z ∈ interior Kr ↔ y ∈ interior K := by
      rw [mem_interior_iff_mem_nhds, mem_interior_iff_mem_nhds]
      change (Subtype.val : R → U) ⁻¹' K ∈ nhds z ↔ K ∈ nhds y
      rw [preimage_coe_mem_nhds_subtype,
        nhdsWithin_eq_nhds.mpr (mem_interior_iff_mem_nhds.mp hy)]
    exact hmem.trans (not_congr hint)
  let u : OpenPartialHomeomorph U X :=
    U.isOpen.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : U → X)
  have hus : u.source = univ := rfl
  have huK : u.IsImage K B := by
    intro y _
    change (y : X) ∈ (Subtype.val : U → X) '' K ↔ y ∈ K
    exact Subtype.val_injective.mem_set_image
  have huR : u.IsImage R H := by
    intro y _
    rfl
  have hB : IsCompact B := hK.image continuous_subtype_val
  have hBreg : closure (interior B) = B := by
    apply Subset.antisymm (closure_minimal interior_subset hB.isClosed)
    rintro x ⟨y, hy, rfl⟩
    have hy' : y ∈ closure (interior K) := hKD.closure_interior.symm ▸ hy
    exact closure_mono (U.isOpen.isOpenMap_subtype_val.image_interior_subset K)
      (image_closure_subset_closure_image continuous_subtype_val ⟨y, hy', rfl⟩)
  have hDformula : D = (interior B)ᶜ ∩ interior H := by
    ext x
    by_cases hxU : x ∈ (U : Set X)
    · let y : U := ⟨x, hxU⟩
      have hyH : x ∈ interior H ↔ y ∈ interior R :=
        huR.interior.apply_mem_iff (x := y) (hus.symm ▸ mem_univ y)
      have hyB : x ∈ interior B ↔ y ∈ interior K :=
        huK.interior.apply_mem_iff (x := y) (hus.symm ▸ mem_univ y)
      constructor
      · intro hx
        have hxi := hDint hx
        exact ⟨fun hb => (hDlocal y (hyH.mp hxi)).mp hx (hyB.mp hb), hxi⟩
      · intro hx
        exact (hDlocal y (hyH.mp hx.2)).mpr (fun hk => hx.1 (hyB.mpr hk))
    · have hxB : x ∉ interior B := by
        rintro hx
        obtain ⟨y, _, rfl⟩ := interior_subset hx
        exact hxU y.property
      constructor
      · intro hx
        exact ⟨hxB, hDint hx⟩
      · intro hx
        refine ⟨interior_subset hx.2, ?_⟩
        rintro ⟨y, _, rfl⟩
        exact hxU y.property
  have hfrontB : frontier B = (Subtype.val : U → X) '' frontier K := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, _, rfl⟩ := hB.isClosed.frontier_subset hx
      exact ⟨y, (huK.frontier.apply_mem_iff (hus.symm ▸ mem_univ y)).mp hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact (huK.frontier.apply_mem_iff (hus.symm ▸ mem_univ y)).mpr hy
  have hfrontComp : frontier (interior B)ᶜ = frontier B := by
    rw [frontier_compl]
    simp only [frontier, hBreg, interior_interior, hB.isClosed.closure_eq]
  have hfrontDO : frontier D = frontier B ∩ interior H := by
    have hsub : frontier D ⊆ interior H := hDcompact.isClosed.frontier_subset.trans hDint
    calc
      frontier D = frontier D ∩ interior H := (inter_eq_left.mpr hsub).symm
      _ = frontier (interior B)ᶜ ∩ interior H := by
        rw [hDformula]
        exact frontier_inter_open_inter isOpen_interior
      _ = frontier B ∩ interior H := by rw [hfrontComp]
  have hfrontD : frontier D = (Subtype.val : U → X) '' S := by
    rw [hfrontDO, hfrontB, hfront]
    apply Subset.antisymm
    · rintro x ⟨⟨y, hy | hy, rfl⟩, hxH⟩
      · have hyf : (y : X) ∈ frontier H := hfrontR.subset hy
        exact (hyf.2 hxH).elim
      · exact ⟨y, hy, rfl⟩
    · rintro x ⟨y, hy, rfl⟩
      exact ⟨⟨y, Or.inr hy, rfl⟩,
        (huR.interior.apply_mem_iff (hus.symm ▸ mem_univ y)).mpr (hS hy)⟩
  exact ⟨hDcompact, hDint, hfrontD, hDlocal⟩

end PoincareConjecture.M76
