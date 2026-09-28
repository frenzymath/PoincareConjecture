import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_BoxSpatialInverse
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_CylinderSpatialInverse
import PoincareConjecture.Proofs.M12.GeneralizedCylinderFactor

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

private theorem originalBox_point_transport (b : F.box_index)
    {t t' : ℝ} (h : t = t') (ht : t ∈ (F.box b).interval)
    (ht' : t' ∈ (F.box b).interval) (y : (F.box b).carrier.carrier) :
    (⟨t, (F.box b).forward t ht y⟩ : F.point) =
      (⟨t', (F.box b).forward t' ht' y⟩ : F.point) := by
  subst t'
  rfl

theorem rawCylinder_factor_spatial_inverse
    (p : (R.timeIntervals.interval (cylinderPhysicalInterval a q e.scale_pos J)).Point × U)
    (D : RawCylinderLocalFactor R e p) :
    ∃ psi : (F.box D.box).carrier.carrier → C.carrier,
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ psi (D.spatial p.2) ∧
        (fun z => psi (D.spatial z)) =ᶠ[𝓝 p.2] Subtype.val := by
  let s := cylinderClockHomeomorph a q e.scale_pos J p.1
  let T := a + s.val / q
  have hT : T = p.1.val := parabolicTimeInv_parabolicTime q e.scale_pos a p.1.val
  have ht : T ∈ (F.box D.box).interval := hT.symm ▸ D.box_subset D.center_mem
  have hfixed : (fun z : U => rawCylinderMap R e (p.1, z)) =ᶠ[𝓝 p.2]
      (fun z => originalBoxMap F R D.box
        (⟨p.1.val, D.box_subset D.center_mem⟩, D.spatial z)) :=
    D.local_eq.comp_tendsto (continuous_const.prodMk continuous_id).continuousAt.tendsto
  have hspatial {z : U} (hz : rawCylinderMap R e (p.1, z) =
      originalBoxMap F R D.box (⟨p.1.val, D.box_subset D.center_mem⟩, D.spatial z)) :
      e.forward s.val s.property z.val = (F.box D.box).forward T ht (D.spatial z) := by
    have hbox := originalBox_point_transport D.box hT ht
      (D.box_subset D.center_mem) (D.spatial z)
    have hpoint := hz.trans hbox.symm
    change (⟨T, e.forward s.val s.property z.val⟩ : F.point) =
      (⟨T, (F.box D.box).forward T ht (D.spatial z)⟩ : F.point) at hpoint
    exact eq_of_heq (Sigma.mk.inj_iff.mp hpoint).2
  let psi : (F.box D.box).carrier.carrier → C.carrier :=
    e.inverse s.val s.property ∘ (F.box D.box).forward T ht
  have hbase := hspatial hfixed.eq_of_nhds
  have hinv : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (e.inverse s.val s.property)
      ((F.box D.box).forward T ht (D.spatial p.2)) := by
    rw [← hbase]
    exact rawCylinder_inverse_contMDiffAt e s p.2
  refine ⟨psi, hinv.comp _ ((F.box D.box).forward_smooth T ht _), ?_⟩
  filter_upwards [hfixed] with z hz
  change e.inverse s.val s.property ((F.box D.box).forward T ht (D.spatial z)) = z.val
  rw [← hspatial hz]
  exact e.left_inverse s.val s.property z.property

theorem rawCylinder_spatial_local_inverse
    (hI : (cylinderPhysicalInterval a q e.scale_pos J).domain ⊆ F.interval)
    (p : (R.timeIntervals.interval (cylinderPhysicalInterval a q e.scale_pos J)).Point × U) :
    ∃ phi : R.spacetime.Point → C.carrier,
      ContMDiffAt (spacetimeModel 3) (𝓡 3) ∞ phi (rawCylinderMap R e p) ∧
        (fun z => phi (rawCylinderMap R e z)) =ᶠ[𝓝 p] (fun z => z.2.val) := by
  obtain ⟨D⟩ := rawCylinderLocalFactor_exists R e hI p
  let pL : (R.timeIntervals.interval D.interval).Point × U :=
    (⟨p.1.val, D.center_mem⟩, p.2)
  let pB : (R.timeIntervals.interval (boxInterval F D.box)).Point ×
      (F.box D.box).carrier.carrier :=
    (⟨p.1.val, D.box_subset D.center_mem⟩, D.spatial p.2)
  let inc := spacetimeIntervalInclusion (R.timeIntervals.interval D.interval)
    (R.timeIntervals.interval (cylinderPhysicalInterval a q e.scale_pos J)) D.subset
  let intoBox : (R.timeIntervals.interval D.interval).Point × U →
      (R.timeIntervals.interval (boxInterval F D.box)).Point ×
        (F.box D.box).carrier.carrier := fun z =>
    (spacetimeIntervalInclusion (R.timeIntervals.interval D.interval)
      (R.timeIntervals.interval (boxInterval F D.box)) D.box_subset z.1, D.spatial z.2)
  obtain ⟨phiB, hphiB, hphiBeq⟩ := originalBox_spatial_local_inverse R D.box pB
  obtain ⟨psi, hpsi, hpsieq⟩ := rawCylinder_factor_spatial_inverse R e p D
  have hpoint : rawCylinderMap R e p = originalBoxMap F R D.box pB :=
    D.local_eq.eq_of_nhds
  have hphiBpoint : phiB (originalBoxMap F R D.box pB) = D.spatial p.2 :=
    hphiBeq.eq_of_nhds
  have hphi : ContMDiffAt (spacetimeModel 3) (𝓡 3) ∞ (psi ∘ phiB)
      (rawCylinderMap R e p) := by
    rw [hpoint]
    exact (hphiBpoint.symm ▸ hpsi).comp _ hphiB
  have htime := R.timeIntervals.inclusion_smooth D.interval (boxInterval F D.box)
    D.box_subset
  have hsnd : ContinuousAt
      (Prod.snd : (R.timeIntervals.interval D.interval).Point × U → U) pL :=
    continuous_snd.continuousAt
  have hinto : ContinuousAt intoBox pL :=
    (htime.continuous.continuousAt.comp continuous_fst.continuousAt).prodMk
      (D.spatial_smooth.continuousAt.comp (x := pL) (f := Prod.snd) hsnd)
  have hlocal : (fun z => (psi ∘ phiB) (rawCylinderMap R e (Prod.map inc id z)))
      =ᶠ[𝓝 pL] (fun z => z.2.val) := by
    filter_upwards [D.local_eq, hinto.tendsto.eventually hphiBeq,
      continuous_snd.continuousAt.tendsto.eventually hpsieq] with z hz hzb hzs
    change psi (phiB (rawCylinderMap R e (Prod.map inc id z))) = z.2.val
    change rawCylinderMap R e (Prod.map inc id z) =
      originalBoxMap F R D.box (intoBox z) at hz
    rw [hz, hzb]
    exact hzs
  have hinc : IsLocalDiffeomorph (𝓡∂ 1) (𝓡∂ 1) ∞ inc :=
    R.interval_localDiffeomorph _ _ D.subset D.relatively_open
  have hmap : map (Prod.map inc (id : U → U)) (𝓝 pL) = 𝓝 p := by
    exact (hinc.isOpenMap.prodMap IsOpenMap.id).map_nhds_eq
      (hinc.contMDiff.continuous.prodMap continuous_id).continuousAt
  refine ⟨psi ∘ phiB, hphi, ?_⟩
  rw [← hmap]
  exact hlocal

theorem rawCylinder_lift_spatial_contMDiffWithinAt
    (hI : (cylinderPhysicalInterval a q e.scale_pos J).domain ⊆ F.interval)
    {gamma : ℝ → R.spacetime.Point}
    {beta : ℝ → (R.timeIntervals.interval
      (cylinderPhysicalInterval a q e.scale_pos J)).Point × U}
    {B : Set ℝ} {r : ℝ} (hr : r ∈ B)
    (hgamma : ContMDiffWithinAt 𝓘(ℝ, ℝ) (spacetimeModel 3) 1 gamma B r)
    (hbeta : ContinuousWithinAt beta B r)
    (heq : EqOn (rawCylinderMap R e ∘ beta) gamma B) :
    ContMDiffWithinAt 𝓘(ℝ, ℝ) (𝓡 3) 1 (fun t => (beta t).2.val) B r := by
  obtain ⟨phi, hphi, hleft⟩ := rawCylinder_spatial_local_inverse R e hI (beta r)
  have hpoint : rawCylinderMap R e (beta r) = gamma r := heq hr
  have hcomp : ContMDiffWithinAt 𝓘(ℝ, ℝ) (𝓡 3) 1 (phi ∘ gamma) B r :=
    ((hpoint ▸ hphi).of_le (by simp)).comp_contMDiffWithinAt r hgamma
  refine hcomp.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hbeta.tendsto.eventually hleft, self_mem_nhdsWithin] with t ht hBt
    change (beta t).2.val = phi (gamma t)
    rw [← heq hBt]
    exact ht.symm
  · change (beta r).2.val = phi (gamma r)
    rw [← hpoint]
    exact hleft.eq_of_nhds.symm

theorem exists_rawCylinder_lift
    (hI : (cylinderPhysicalInterval a q e.scale_pos J).domain ⊆ F.interval)
    {gamma : ℝ → R.spacetime.Point} {B : Set ℝ} (hB : B.Nonempty)
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (spacetimeModel 3) 1 gamma B)
    (himage : MapsTo gamma B (range (rawCylinderMap R e))) :
    ∃ beta : ℝ → (R.timeIntervals.interval
        (cylinderPhysicalInterval a q e.scale_pos J)).Point × U,
      EqOn (rawCylinderMap R e ∘ beta) gamma B ∧ ContinuousOn beta B ∧
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (fun t => (beta t).2.val) B ∧
          ∀ t ∈ B, (beta t).1.val = R.spacetime.timeFunction (gamma t) := by
  classical
  obtain ⟨r, hr⟩ := hB
  obtain ⟨p, hp⟩ := himage hr
  let : Nonempty ((R.timeIntervals.interval
      (cylinderPhysicalInterval a q e.scale_pos J)).Point × U) := ⟨p⟩
  let beta := Function.invFun (rawCylinderMap R e) ∘ gamma
  have heq : EqOn (rawCylinderMap R e ∘ beta) gamma B := by
    intro t ht
    exact Function.invFun_eq (himage ht)
  have hcomp : ContinuousOn (rawCylinderMap R e ∘ beta) B :=
    hgamma.continuousOn.congr (fun t ht => heq ht)
  have hbeta : ContinuousOn beta B :=
    (rawCylinderMap_embedding R e).isInducing.continuousOn_iff.mpr hcomp
  refine ⟨beta, heq, hbeta, ?_, ?_⟩
  · intro t ht
    exact rawCylinder_lift_spatial_contMDiffWithinAt R e hI ht (hgamma t ht)
      (hbeta t ht) heq
  · intro t ht
    rw [← rawCylinderMap_time R e (beta t)]
    exact congrArg R.spacetime.timeFunction (heq ht)

end PoincareConjecture.Proofs.M46
