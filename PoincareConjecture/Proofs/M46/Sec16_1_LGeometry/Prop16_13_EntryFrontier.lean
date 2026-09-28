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
  {C : GeneralizedSliceCarrier.{u}} {origin scale : ℝ} {J : SpacetimeInterval}
  {U : TopologicalSpace.Opens C.carrier}
  (e : GeneralizedFlowCylinder F C origin scale J.domain U)

theorem rawCylinder_completed_coordinate_eq
    {a b r : ℝ} (hab : a < b) (hr : r ∈ Icc a b)
    {gamma : ℝ → R.spacetime.Point} {xi : ℝ → C.carrier}
    (hgamma : ContinuousOn gamma (Icc a b)) (hxi : ContinuousOn xi (Icc a b))
    (beta : ℝ → (R.timeIntervals.interval
      (cylinderPhysicalInterval origin scale e.scale_pos J)).Point × U)
    (heq : EqOn (rawCylinderMap R e ∘ beta) gamma (Ioo a b))
    (hcoordinate : EqOn (fun t => (beta t).2.val) xi (Ioo a b))
    (p : (R.timeIntervals.interval
      (cylinderPhysicalInterval origin scale e.scale_pos J)).Point × U)
    (hp : gamma r = rawCylinderMap R e p) : xi r = p.2.val := by
  let : NeBot (𝓝[Ioo a b] r) := mem_closure_iff_nhdsWithin_neBot.mp
    (by simpa only [closure_Ioo hab.ne] using hr)
  have hg := (hgamma r hr).mono Ioo_subset_Icc_self
  have hx := (hxi r hr).mono Ioo_subset_Icc_self
  have hraw : Tendsto (rawCylinderMap R e ∘ beta) (𝓝[Ioo a b] r)
      (𝓝 (rawCylinderMap R e p)) := by
    rw [← hp]
    apply hg.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (heq ht).symm
  have hbeta : Tendsto beta (𝓝[Ioo a b] r) (𝓝 p) :=
    (rawCylinderMap_embedding R e).isInducing.tendsto_nhds_iff.mpr hraw
  have hspatial : Tendsto (fun t => (beta t).2.val) (𝓝[Ioo a b] r) (𝓝 p.2.val) :=
    (continuous_subtype_val.comp continuous_snd).continuousAt.tendsto.comp hbeta
  have hfinal : Tendsto xi (𝓝[Ioo a b] r) (𝓝 p.2.val) := by
    apply hspatial.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hcoordinate ht
  exact tendsto_nhds_unique hx hfinal

theorem rawCylinder_completed_endpoint_eq
    {a b r : ℝ} (hab : a < b) (hr : r ∈ Icc a b)
    {gamma : ℝ → R.spacetime.Point} {xi : ℝ → C.carrier}
    (hgamma : ContinuousOn gamma (Icc a b)) (hxi : ContinuousOn xi (Icc a b))
    (beta : ℝ → (R.timeIntervals.interval
      (cylinderPhysicalInterval origin scale e.scale_pos J)).Point × U)
    (heq : EqOn (rawCylinderMap R e ∘ beta) gamma (Ioo a b))
    (hcoordinate : EqOn (fun t => (beta t).2.val) xi (Ioo a b))
    (hclock : ∀ t ∈ Ioo a b, (beta t).1.val = R.spacetime.timeFunction (gamma t))
    (hrclock : R.spacetime.timeFunction (gamma r) ∈
      (cylinderPhysicalInterval origin scale e.scale_pos J).domain)
    (hrsource : xi r ∈ U) :
    gamma r = rawCylinderMap R e
      (⟨R.spacetime.timeFunction (gamma r), hrclock⟩, ⟨xi r, hrsource⟩) := by
  let : ChartedSpace (ModelProd (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin 3)))
      F.point := R.spacetime.chartedSpace
  let : NeBot (𝓝[Ioo a b] r) := mem_closure_iff_nhdsWithin_neBot.mp
    (by simpa only [closure_Ioo hab.ne] using hr)
  have hg := (hgamma r hr).mono Ioo_subset_Icc_self
  have hx := (hxi r hr).mono Ioo_subset_Icc_self
  have htime : Tendsto (fun t => (beta t).1) (𝓝[Ioo a b] r)
      (𝓝 (⟨R.spacetime.timeFunction (gamma r), hrclock⟩ :
        (R.timeIntervals.interval
          (cylinderPhysicalInterval origin scale e.scale_pos J)).Point)) := by
    apply Topology.IsInducing.subtypeVal.tendsto_nhds_iff.mpr
    apply (R.spacetime.time_smooth.continuous.continuousAt.tendsto.comp hg).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hclock t ht).symm
  have hspace : Tendsto (fun t => (beta t).2) (𝓝[Ioo a b] r)
      (𝓝 (⟨xi r, hrsource⟩ : U)) := by
    apply Topology.IsInducing.subtypeVal.tendsto_nhds_iff.mpr
    apply hx.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (hcoordinate ht).symm
  have hraw := (rawCylinderMap_embedding R e).continuous.continuousAt.tendsto.comp
    (htime.prodMk_nhds hspace)
  have hfinal : Tendsto gamma (𝓝[Ioo a b] r)
      (𝓝 (rawCylinderMap R e
        (⟨R.spacetime.timeFunction (gamma r), hrclock⟩, ⟨xi r, hrsource⟩))) := by
    apply hraw.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact heq ht
  exact tendsto_nhds_unique hg hfinal

theorem rawCylinder_entry_coordinate_mem_frontier
    {a b : ℝ} (hab : a < b)
    {gamma : ℝ → R.spacetime.Point} {xi : ℝ → C.carrier}
    (hgamma : ContinuousOn gamma (Icc a b)) (hxi : ContinuousOn xi (Icc a b))
    (beta : ℝ → (R.timeIntervals.interval
      (cylinderPhysicalInterval origin scale e.scale_pos J)).Point × U)
    (heq : EqOn (rawCylinderMap R e ∘ beta) gamma (Ioo a b))
    (hcoordinate : EqOn (fun t => (beta t).2.val) xi (Ioo a b))
    (hclock : ∀ t ∈ Ioo a b, (beta t).1.val = R.spacetime.timeFunction (gamma t))
    (haclock : R.spacetime.timeFunction (gamma a) ∈
      (cylinderPhysicalInterval origin scale e.scale_pos J).domain)
    (hout : gamma a ∉ range (rawCylinderMap R e)) : xi a ∈ frontier (U : Set C.carrier) := by
  have hnot : xi a ∉ U := by
    intro hU
    exact hout ⟨_, (rawCylinder_completed_endpoint_eq R e hab ⟨le_rfl, hab.le⟩
      hgamma hxi beta heq hcoordinate hclock haclock hU).symm⟩
  have hmaps : MapsTo xi (Ioo a b) U := by
    intro t ht
    rw [← hcoordinate ht]
    exact (beta t).2.property
  have hcl := hmaps.closure_of_continuousOn (by
    simpa only [closure_Ioo hab.ne] using hxi)
  have ha : a ∈ closure (Ioo a b) := by
    simp only [closure_Ioo hab.ne, mem_Icc]
    exact ⟨le_rfl, hab.le⟩
  rw [frontier, U.isOpen.interior_eq]
  exact ⟨hcl ha, hnot⟩

end PoincareConjecture.Proofs.M46
