import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Compat.GeneralizedEquation
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.LGeometry.CapEntry.CylinderOpenImage

/-!
# Actual cylinder image neighborhoods at included time endpoints

Proposition 16.13 and Lemma 16.15, pp. 377-381. At an included birth
point the tracked image contains a neighborhood relative to its actual
physical clock interval. Local product factorization proves this
without an inverse-function theorem at a manifold boundary.
-/

set_option autoImplicit false
-- The selected interval charts retain their actual subtype topologies.
set_option backward.isDefEq.respectTransparency false

open Set Filter Function
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.Proofs.M12
end PoincareMT.Proofs.M12
open PoincareMT.EpochExtension.Spacetime
local notation "GeneralizedFlowCarrierConclusion" => PoincareMT.GeneralizedFlowCarrierConclusionWithInterval

namespace PoincareMT.Proofs.M46

open PoincareMT.Proofs.M12

private theorem interval_inclusion_map_nhds
    {L B K : Set ℝ} (hLK : L ⊆ K) (hLB : L ⊆ B)
    (hopen : IsOpen {t : K | t.val ∈ L}) (p : L) :
    map (Set.inclusion hLB) (𝓝 p) =
      𝓝[{t : B | t.val ∈ K}] (Set.inclusion hLB p) := by
  obtain ⟨O, hO, hLO⟩ := isOpen_induced_iff.mp hopen
  have hrange : range (Set.inclusion hLB) = {t : B | t.val ∈ L} := by
    ext t
    constructor
    · rintro ⟨s, rfl⟩
      exact s.property
    · intro ht
      exact ⟨⟨t.val, ht⟩, rfl⟩
  have hpO : p.val ∈ O := by
    have hp : (⟨p.val, hLK p.property⟩ : K) ∈ {t : K | t.val ∈ L} := p.property
    rwa [← hLO] at hp
  have hemb : Topology.IsEmbedding (Set.inclusion hLB) := Topology.IsEmbedding.inclusion hLB
  have hmap := hemb.map_nhds_eq p
  rw [hmap, hrange]
  apply nhdsWithin_eq_nhdsWithin (s := (Subtype.val : B → ℝ) ⁻¹' O) hpO
    (hO.preimage continuous_subtype_val)
  ext t
  constructor
  · rintro ⟨htL, htO⟩
    exact ⟨hLK htL, htO⟩
  · rintro ⟨htK, htO⟩
    refine ⟨?_, htO⟩
    have ht : (⟨t.val, htK⟩ : K) ∈ (Subtype.val : K → ℝ) ⁻¹' O := htO
    rwa [hLO] at ht

variable {F : GeneralizedRicciFlowData.{u}}
  (R : GeneralizedFlowCarrierConclusion (flowBoxAtlas F))
  {C : GeneralizedSliceCarrier.{u}} {a q : ℝ} {J : SpacetimeInterval}
  {U : TopologicalSpace.Opens C.carrier}
  (e : GeneralizedFlowCylinder F C a q J.domain U)

/-- The actual raw-cylinder image contains the whole local clock strip
at every included source point, including a regular birth endpoint.
Source: Proposition 16.13 and Lemma 16.15, pp. 377-381. -/
theorem rawCylinder_map_nhds_eq_nhdsWithin_clock
    (hI : (cylinderPhysicalInterval a q e.scale_pos J).domain ⊆ F.interval)
    (p : (R.timeIntervals.interval (cylinderPhysicalInterval a q e.scale_pos J)).Point × U) :
    map (rawCylinderMap R e) (𝓝 p) =
      𝓝[R.spacetime.timeFunction ⁻¹'
        (cylinderPhysicalInterval a q e.scale_pos J).domain] (rawCylinderMap R e p) := by
  obtain ⟨D⟩ := rawCylinderLocalFactor_exists R e hI p
  let K := cylinderPhysicalInterval a q e.scale_pos J
  let pL : (R.timeIntervals.interval D.interval).Point × U :=
    (⟨p.1.val, D.center_mem⟩, p.2)
  let pB : (R.timeIntervals.interval (boxInterval F D.box)).Point ×
      (F.box D.box).carrier.carrier :=
    (⟨p.1.val, D.box_subset D.center_mem⟩, D.spatial p.2)
  let inc := spacetimeIntervalInclusion (R.timeIntervals.interval D.interval)
    (R.timeIntervals.interval K) D.subset
  let incB := spacetimeIntervalInclusion (R.timeIntervals.interval D.interval)
    (R.timeIntervals.interval (boxInterval F D.box)) D.box_subset
  have hinc : IsLocalDiffeomorph (𝓡∂ 1) (𝓡∂ 1) ∞ inc :=
    R.interval_localDiffeomorph _ _ D.subset D.relatively_open
  have hmap : map (Prod.map inc (id : U → U)) (𝓝 pL) = 𝓝 p :=
    (hinc.isOpenMap.prodMap IsOpenMap.id).map_nhds_eq
      (hinc.contMDiff.continuous.prodMap continuous_id).continuousAt
  have hspace : map D.spatial (𝓝 p.2) = 𝓝 (D.spatial p.2) := by
    apply Poincare.map_nhds_eq_of_contMDiffAt_mfderiv_bijective D.spatial_smooth
    let L : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
      LinearEquiv.ofInjectiveEndo
        (mfderiv (𝓡 3) (𝓡 3) D.spatial p.2).toLinearMap D.spatial_injective
    exact L.bijective
  have htime : map incB (𝓝 pL.1) =
      𝓝[{t : (R.timeIntervals.interval (boxInterval F D.box)).Point |
        t.val ∈ K.domain}] pB.1 :=
    interval_inclusion_map_nhds D.subset D.box_subset D.relatively_open pL.1
  let V : Set ((R.timeIntervals.interval (boxInterval F D.box)).Point ×
      (F.box D.box).carrier.carrier) := {z | z.1.val ∈ K.domain}
  have hbox : map (Prod.map incB D.spatial) (𝓝 pL) = 𝓝[V] pB := by
    rw [nhds_prod_eq, ← Filter.prod_map_map_eq', htime, hspace]
    have hV : V = {t | t.val ∈ K.domain} ×ˢ univ := by
      ext z
      simp only [V, mem_ofPred_eq, mem_prod, mem_univ, and_true]
    rw [hV, nhdsWithin_prod_eq, nhdsWithin_univ]
  have hbase : rawCylinderMap R e p = originalBoxMap F R D.box pB :=
    D.local_eq.eq_of_nhds
  calc
    _ = map (rawCylinderMap R e ∘ Prod.map inc id) (𝓝 pL) := by
      rw [← map_map, hmap]
    _ = map (originalBoxMap F R D.box ∘ Prod.map incB D.spatial) (𝓝 pL) :=
      Filter.map_congr D.local_eq
    _ = map (originalBoxMap F R D.box) (𝓝[V] pB) := by rw [← map_map, hbox]
    _ = 𝓝[R.spacetime.timeFunction ⁻¹' K.domain]
        (originalBoxMap F R D.box pB) :=
      (F.box_openEmbedding D.box).map_nhdsWithin_preimage_eq
        (R.spacetime.timeFunction ⁻¹' K.domain) pB
    _ = _ := congrArg (nhdsWithin · (R.spacetime.timeFunction ⁻¹' K.domain)) hbase.symm

/-- Relative capture is an actual neighborhood membership and can be
pulled back by any continuous path whose clock stays in the included
physical interval. Source: Lemma 16.15, pp. 379-381. -/
theorem rawCylinder_range_mem_nhdsWithin_clock
    (hI : (cylinderPhysicalInterval a q e.scale_pos J).domain ⊆ F.interval)
    (p : (R.timeIntervals.interval (cylinderPhysicalInterval a q e.scale_pos J)).Point × U) :
    range (rawCylinderMap R e) ∈
      𝓝[R.spacetime.timeFunction ⁻¹'
        (cylinderPhysicalInterval a q e.scale_pos J).domain] (rawCylinderMap R e p) := by
  rw [← rawCylinder_map_nhds_eq_nhdsWithin_clock R e hI p]
  exact range_mem_map

end PoincareMT.Proofs.M46
