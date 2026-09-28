import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_CylinderLocalInverse

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter Function
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.Proofs.M12

variable {F : GeneralizedRicciFlowData.{u}}
  (R : GeneralizedFlowCarrierConclusion (flowBoxAtlas F))
  {C : GeneralizedSliceCarrier.{u}} {a q : ℝ} {J : SpacetimeInterval}
  {U : TopologicalSpace.Opens C.carrier}
  (e : GeneralizedFlowCylinder F C a q J.domain U)

theorem rawCylinder_isOpenEmbedding
    (hI : (cylinderPhysicalInterval a q e.scale_pos J).domain ⊆ F.interval)
    (hopen : IsOpen (cylinderPhysicalInterval a q e.scale_pos J).domain) :
    Topology.IsOpenEmbedding (rawCylinderMap R e) := by
  have hnhds (p :
      (R.timeIntervals.interval (cylinderPhysicalInterval a q e.scale_pos J)).Point × U) :
      map (rawCylinderMap R e) (𝓝 p) = 𝓝 (rawCylinderMap R e p) := by
    obtain ⟨D⟩ := rawCylinderLocalFactor_exists R e hI p
    let pL : (R.timeIntervals.interval D.interval).Point × U :=
      (⟨p.1.val, D.center_mem⟩, p.2)
    let pB : (R.timeIntervals.interval (boxInterval F D.box)).Point ×
        (F.box D.box).carrier.carrier :=
      (⟨p.1.val, D.box_subset D.center_mem⟩, D.spatial p.2)
    let inc := spacetimeIntervalInclusion (R.timeIntervals.interval D.interval)
      (R.timeIntervals.interval (cylinderPhysicalInterval a q e.scale_pos J)) D.subset
    let incB := spacetimeIntervalInclusion (R.timeIntervals.interval D.interval)
      (R.timeIntervals.interval (boxInterval F D.box)) D.box_subset
    have hLopen : IsOpen D.interval.domain := by
      have h := hopen.isOpenEmbedding_subtypeVal.isOpenMap _ D.relatively_open
      have heq : (Subtype.val :
          (cylinderPhysicalInterval a q e.scale_pos J).domain → ℝ) ''
          {t | t.val ∈ D.interval.domain} = D.interval.domain := by
        ext t
        constructor
        · rintro ⟨s, hs, rfl⟩
          exact hs
        · intro ht
          exact ⟨⟨t, D.subset ht⟩, ht, rfl⟩
      rwa [heq] at h
    have hinc : IsLocalDiffeomorph (𝓡∂ 1) (𝓡∂ 1) ∞ inc :=
      R.interval_localDiffeomorph _ _ D.subset D.relatively_open
    have hincB : IsLocalDiffeomorph (𝓡∂ 1) (𝓡∂ 1) ∞ incB :=
      R.interval_localDiffeomorph _ _ D.box_subset (hLopen.preimage continuous_subtype_val)
    have hmap : map (Prod.map inc (id : U → U)) (𝓝 pL) = 𝓝 p :=
      (hinc.isOpenMap.prodMap IsOpenMap.id).map_nhds_eq
        (hinc.contMDiff.continuous.prodMap continuous_id).continuousAt
    have hspace : map D.spatial (𝓝 p.2) = 𝓝 (D.spatial p.2) := by
      apply Poincare.map_nhds_eq_of_contMDiffAt_mfderiv_bijective D.spatial_smooth
      let L : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
        LinearEquiv.ofInjectiveEndo
          (mfderiv (𝓡 3) (𝓡 3) D.spatial p.2).toLinearMap D.spatial_injective
      exact L.bijective
    have htime : map incB (𝓝 pL.1) = 𝓝 pB.1 :=
      hincB.isOpenMap.map_nhds_eq hincB.contMDiff.continuous.continuousAt
    have hbox : map (Prod.map incB D.spatial) (𝓝 pL) = 𝓝 pB := by
      rw [nhds_prod_eq, ← Filter.prod_map_map_eq', htime, hspace, ← nhds_prod_eq]
    have hbase : rawCylinderMap R e p = originalBoxMap F R D.box pB :=
      D.local_eq.eq_of_nhds
    calc
      _ = map (rawCylinderMap R e ∘ Prod.map inc id) (𝓝 pL) := by
        rw [← map_map, hmap]
      _ = map (originalBoxMap F R D.box ∘ Prod.map incB D.spatial) (𝓝 pL) :=
        Filter.map_congr D.local_eq
      _ = map (originalBoxMap F R D.box) (𝓝 pB) := by rw [← map_map, hbox]
      _ = 𝓝 (originalBoxMap F R D.box pB) := (F.box_openEmbedding D.box).map_nhds_eq pB
      _ = _ := congrArg nhds hbase.symm
  have hop : IsOpenMap (rawCylinderMap R e) := by
    intro V hV
    apply isOpen_iff_mem_nhds.mpr
    rintro y ⟨p, hp, rfl⟩
    rw [← hnhds p]
    exact image_mem_map (hV.mem_nhds hp)
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (rawCylinderMap_embedding R e).continuous (rawCylinderMap_embedding R e).injective hop

end PoincareConjecture.Proofs.M46
