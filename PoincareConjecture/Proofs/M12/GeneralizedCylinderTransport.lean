import PoincareConjecture.Proofs.M12.GeneralizedCylinderFactor









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M12

open PoincareConjecture.Proofs.M11

variable {F : GeneralizedRicciFlowData.{u}}
  (R : GeneralizedFlowCarrierConclusion (flowBoxAtlas F))
  {C : GeneralizedSliceCarrier.{u}} {a q : ℝ} {J : SpacetimeInterval}
  {U : TopologicalSpace.Opens C.carrier}
  (e : GeneralizedFlowCylinder F C a q J.domain U)
  (hI : (cylinderPhysicalInterval a q e.scale_pos J).domain ⊆ F.interval)

include hI

theorem rawCylinderMap_smooth :
    ContMDiff (spacetimeModel 3) (spacetimeModel 3) ∞ (rawCylinderMap R e) := by
  intro p
  obtain ⟨D⟩ := rawCylinderLocalFactor_exists R e hI p
  let pL : (R.timeIntervals.interval D.interval).Point × U :=
    (⟨p.1.val, D.center_mem⟩, p.2)
  have hlocal : ContMDiffAt (spacetimeModel 3) (spacetimeModel 3) ∞
      (fun z : (R.timeIntervals.interval D.interval).Point × U =>
        rawCylinderMap R e
          (spacetimeIntervalInclusion (R.timeIntervals.interval D.interval)
            (R.timeIntervals.interval (cylinderPhysicalInterval a q e.scale_pos J)) D.subset z.1,
            z.2)) pL := by
    have ht := R.timeIntervals.inclusion_smooth D.interval (boxInterval F D.box) D.box_subset
    have hprod := ((ht pL.1).comp pL contMDiffAt_fst).prodMk
      (D.spatial_smooth.comp pL contMDiffAt_snd)
    exact ((originalBoxMap_smooth F R D.box _).comp pL hprod).congr_of_eventuallyEq D.local_eq
  exact selectedInterval_product_smoothAt_of_local R _ D.interval D.subset
    D.relatively_open pL (rawCylinderMap R e) hlocal

theorem rawCylinderMap_differential_injective
    (p : (R.timeIntervals.interval (cylinderPhysicalInterval a q e.scale_pos J)).Point × U) :
    Injective (mfderiv (spacetimeModel 3) (spacetimeModel 3) (rawCylinderMap R e) p) := by
  obtain ⟨D⟩ := rawCylinderLocalFactor_exists R e hI p
  let pL : (R.timeIntervals.interval D.interval).Point × U :=
    (⟨p.1.val, D.center_mem⟩, p.2)
  let j := spacetimeIntervalInclusion (R.timeIntervals.interval D.interval)
    (R.timeIntervals.interval (cylinderPhysicalInterval a q e.scale_pos J)) D.subset
  let k := spacetimeIntervalInclusion (R.timeIntervals.interval D.interval)
    (R.timeIntervals.interval (boxInterval F D.box)) D.box_subset
  have hj := (R.timeIntervals.inclusion_smooth D.interval _ D.subset pL.1).mdifferentiableAt
    (by simp)
  have hk := (R.timeIntervals.inclusion_smooth D.interval _ D.box_subset pL.1).mdifferentiableAt
    (by simp)
  have hjsurj : Surjective (mfderiv (spacetimeModel 3) (spacetimeModel 3)
      (Prod.map j (id : U → U)) pL) := by
    rw [mfderiv_prodMap hj mdifferentiableAt_id, mfderiv_id]
    have hlocal := R.interval_localDiffeomorph _ D.interval D.subset D.relatively_open pL.1
    exact Surjective.prodMap
      (hlocal.mfderivToContinuousLinearEquiv (by simp)).surjective (fun v => ⟨v, rfl⟩)
  have hkinj : Injective (mfderiv (spacetimeModel 3) (spacetimeModel 3)
      (Prod.map k D.spatial) pL) := by
    rw [mfderiv_prodMap hk (D.spatial_smooth.mdifferentiableAt (by simp))]
    exact Injective.prodMap
      (intervalInclusion_differential_injective R.timeIntervals _ _ D.box_subset pL.1)
      D.spatial_injective
  have heq := D.local_eq.mfderiv_eq (I := spacetimeModel 3) (I' := spacetimeModel 3)
  change mfderiv (spacetimeModel 3) (spacetimeModel 3)
      (rawCylinderMap R e ∘ Prod.map j id) pL =
    mfderiv (spacetimeModel 3) (spacetimeModel 3)
      (originalBoxMap F R D.box ∘ Prod.map k D.spatial) pL at heq
  have hlocal : Injective (mfderiv (spacetimeModel 3) (spacetimeModel 3)
      (rawCylinderMap R e ∘ Prod.map j id) pL) := by
    rw [heq]
    rw [mfderiv_comp pL ((originalBoxMap_smooth F R D.box _).mdifferentiableAt (by simp))
      (hk.prodMap (D.spatial_smooth.mdifferentiableAt (by simp)))]
    exact (originalBoxMap_differential_injective F R D.box _).comp hkinj
  rw [mfderiv_comp pL ((rawCylinderMap_smooth R e hI _).mdifferentiableAt (by simp))
    (hj.prodMap mdifferentiableAt_id)] at hlocal
  have hc : Injective
    ((mfderiv (spacetimeModel 3) (spacetimeModel 3) (rawCylinderMap R e) p) ∘
      (mfderiv (spacetimeModel 3) (spacetimeModel 3) (Prod.map j id) pL)) := hlocal
  exact hc.of_comp_right hjsurj

noncomputable def rawCylinderTransport :
    CompatibleSpacetimeCylinder R.spacetime
      (R.timeIntervals.interval (cylinderPhysicalInterval a q e.scale_pos J)) U where
  interval_subset := hI
  toSpacetime := rawCylinderMap R e
  embedding := rawCylinderMap_embedding R e
  time_eq := rawCylinderMap_time R e
  worldline_smooth := rawCylinderMap_worldline_smooth R e
  worldline_derivative := rawCylinderMap_worldline_derivative R e
  smooth := rawCylinderMap_smooth R e hI
  differential_injective := rawCylinderMap_differential_injective R e hI

end PoincareConjecture.Proofs.M12
