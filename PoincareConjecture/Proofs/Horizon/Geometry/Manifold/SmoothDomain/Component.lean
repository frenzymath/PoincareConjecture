import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothDomain.Interior
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Interior.LocalPathConnected

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold

variable {m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  {K C : Set M}
  [ChartedSpace (EuclideanHalfSpace (m + 1)) K]
  [IsManifold (𝓡∂ (m + 1)) ∞ K]

theorem exists_connected_smooth_component
    (hK : IsCompact K)
    (hemb : _root_.Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞
      (Subtype.val : K → M))
    (hC : IsConnected C) (hCK : C ⊆ interior K) :
    ∃ (L : Set M) (CS : ChartedSpace (EuclideanHalfSpace (m + 1)) L),
      L ⊆ K ∧ IsCompact L ∧ IsConnected L ∧ C ⊆ interior L ∧
      @IsManifold ℝ _ _ _ _ _ _ (𝓡∂ (m + 1)) ∞ L _ CS ∧
      _root_.Manifold.IsSmoothEmbedding (𝓡∂ (m + 1)) (𝓡 (m + 1)) ∞
        (Subtype.val : L → M) := by
  classical
  obtain ⟨p, hp⟩ := hC.nonempty
  let pK : K := ⟨p, interior_subset (hCK hp)⟩
  let : LocallyPathConnectedSpace K := manifold_locallyPathConnected (I := 𝓡∂ (m + 1))
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let S : TopologicalSpace.Opens K := ⟨connectedComponent pK, isOpen_connectedComponent⟩
  have hS : Nonempty S := ⟨⟨pK, mem_connectedComponent⟩⟩
  let L : Set M := Subtype.val '' (S : Set K)
  let e : S ≃ₜ L := Topology.IsEmbedding.subtypeVal.homeomorphImage (S : Set K)
  let liftChart := fun c : OpenPartialHomeomorph K (EuclideanHalfSpace (m + 1)) =>
    (c.subtypeRestr hS).lift_openEmbedding e.isOpenEmbedding
  let CS : ChartedSpace (EuclideanHalfSpace (m + 1)) L := {
    atlas := liftChart '' IsManifold.maximalAtlas (𝓡∂ (m + 1)) ∞ K
    chartAt := fun x => liftChart (chartAt _ (e.symm x).val)
    mem_chart_source := by
      intro x
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using
        mem_chart_source (EuclideanHalfSpace (m + 1)) (e.symm x).val
    chart_mem_atlas := fun x =>
      ⟨chartAt _ (e.symm x).val, IsManifold.chart_mem_maximalAtlas _, rfl⟩ }
  let := CS
  have hman : IsManifold (𝓡∂ (m + 1)) ∞ L := {
    compatible := by
      rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
      rw [OpenPartialHomeomorph.lift_openEmbedding_trans]
      apply (contDiffGroupoid ∞ (𝓡∂ (m + 1))).mem_of_eqOnSource
        (closedUnderRestriction'
          (StructureGroupoid.compatible_of_mem_maximalAtlas hc hd)
          (c.isOpen_inter_preimage_symm S.isOpen))
      exact c.subtypeRestr_symm_trans_subtypeRestr hS d }
  let := hman
  have hCL : C ⊆ L := by
    change C ⊆ Subtype.val '' connectedComponent pK
    rw [← connectedComponentIn_eq_image pK.property]
    exact
      hC.isPreconnected.subset_connectedComponentIn hp
        (hCK.trans interior_subset)
  have hCLint : C ⊆ interior L := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hCL hx
    rw [mem_interior_iff_mem_nhds]
    have hs := image_mem_map (m := (Subtype.val : K → M)) (S.isOpen.mem_nhds hy)
    rw [Topology.IsEmbedding.subtypeVal.map_nhds_of_mem y (by
      simpa only [Subtype.range_coe] using (mem_interior_iff_mem_nhds.mp (hCK hx)))] at hs
    exact hs
  refine ⟨L, CS, image_subset_iff.mpr (fun y _ => y.property),
    isClosed_connectedComponent.isCompact.image continuous_subtype_val,
    isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn,
    hCLint, hman, ?_⟩
  refine ⟨?_, Topology.IsEmbedding.subtypeVal⟩
  refine ⟨hemb.isImmersion.complement, inferInstance, inferInstance, ?_⟩
  intro x
  have hi := hemb.isImmersion.isImmersionOfComplement_complement (e.symm x).val
  refine _root_.Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    continuous_subtype_val.continuousAt hi.equiv (liftChart hi.domChart) hi.codChart
    ?_ ?_ ?_ hi.codChart_mem_maximalAtlas ?_
  · refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    simpa only [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using
      hi.mem_domChart_source
  · convert hi.mem_codChart_source using 1
    change (x : M) = (e (e.symm x) : M)
    rw [e.apply_symm_apply]
  · exact IsManifold.subset_maximalAtlas ⟨hi.domChart, hi.domChart_mem_maximalAtlas, rfl⟩
  · intro z hz
    rw [OpenPartialHomeomorph.extend_target] at hz
    have hz' : z ∈ (hi.domChart.extend (𝓡∂ (m + 1))).target := by
      rw [OpenPartialHomeomorph.extend_target]
      exact ⟨hi.domChart.subtypeRestr_target_subset hS hz.1, hz.2⟩
    convert hi.writtenInCharts hz' using 1
    dsimp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe_symm]
    apply congrArg (hi.codChart.extend (𝓡 (m + 1)))
    exact congrArg (Subtype.val : K → M) (hi.domChart.subtypeRestr_symm_apply hS hz.1)

end Poincare.Manifold
