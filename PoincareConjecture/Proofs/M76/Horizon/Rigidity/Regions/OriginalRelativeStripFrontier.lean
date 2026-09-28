import PoincareConjecture.Proofs.M76.Rigidity.OriginalRelativeCutFrontier










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.OriginalDiskProduct

variable {X ι : Type*} [TopologicalSpace X] [T2Space X]
  {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
  {R : Set X} {j : (Fin 2 → ℝ) → X}

omit [T2Space X] in
theorem closedStrip_subset (P : OriginalDiskProduct e R j) : P.closedStrip ⊆ R := by
  rintro _ ⟨z, hz, rfl⟩
  exact P.inside ⟨hz.1, by linarith [hz.2.1], by linarith [hz.2.2]⟩


theorem relative_interior_closedStrip (P : OriginalDiskProduct e R j)
    (hR : IsCompact R) (he : PLDomain e R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip)) :
    interior ((Subtype.val : R → X) ⁻¹' P.closedStrip) =
      (Subtype.val : R → X) ⁻¹' P.openStrip := by
  have hUR : P.openStrip ⊆ R :=
    (image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)).trans P.closedStrip_subset
  have hclosure : closure ((Subtype.val : R → X) ⁻¹' P.openStrip) =
      (Subtype.val : R → X) ⁻¹' P.closedStrip := by
    rw [closure_subtype_preimage_of_subset hUR, P.closure_openStrip hopen]
  have hcut : (Subtype.val : R → X) ⁻¹' P.cutCarrier =
      ((Subtype.val : R → X) ⁻¹' P.openStrip)ᶜ := by
    ext x
    exact and_iff_right x.property
  have hreg := P.relative_regular_closed_cut hR he hopen
  rw [hcut, interior_compl, closure_compl] at hreg
  exact compl_injective (by rwa [hclosure] at hreg)



theorem relative_frontier_closedStrip (P : OriginalDiskProduct e R j)
    (hR : IsCompact R) (he : PLDomain e R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip)) :
    frontier ((Subtype.val : R → X) ⁻¹' P.closedStrip) =
      (Subtype.val : R → X) ⁻¹' P.endDisks := by
  have hC : IsClosed ((Subtype.val : R → X) ⁻¹' P.closedStrip) :=
    (P.isCompact_closed_strip (by norm_num : (1 / 2 : ℝ) ≤ 1)).isClosed.preimage
      continuous_subtype_val
  rw [hC.frontier_eq,
    P.relative_interior_closedStrip hR he hopen, ← preimage_sdiff,
    P.closedStrip_sdiff_openStrip]


theorem relative_regular_closed_closedStrip (P : OriginalDiskProduct e R j)
    (hR : IsCompact R) (he : PLDomain e R)
    (hopen : IsOpen ((Subtype.val : R → X) ⁻¹' P.openStrip)) :
    closure (interior ((Subtype.val : R → X) ⁻¹' P.closedStrip)) =
      (Subtype.val : R → X) ⁻¹' P.closedStrip := by
  have hUR : P.openStrip ⊆ R :=
    (image_mono (prod_mono subset_rfl Ioo_subset_Icc_self)).trans P.closedStrip_subset
  rw [P.relative_interior_closedStrip hR he hopen,
    closure_subtype_preimage_of_subset hUR,
    P.closure_openStrip hopen]

end PoincareConjecture.M76.OriginalDiskProduct
