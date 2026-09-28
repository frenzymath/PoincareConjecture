import PoincareConjecture.Proofs.M12
import PoincareConjecture.Proofs.M12.GeneralizedCylinderMetric
import PoincareConjecture.Proofs.M13.OrdinaryFlow
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M30.Cylinder

open PoincareConjecture.Proofs.M12

theorem rescale_physicalInterval_domain (origin scale : ℝ) (hscale : 0 < scale)
    (J : SpacetimeInterval) :
    (parabolicInterval scale hscale origin
      (cylinderPhysicalInterval origin scale hscale J)).domain = J.domain := by
  change parabolicTime scale origin '' (parabolicTimeInv scale origin '' J.domain) = J.domain
  ext s
  constructor
  · rintro ⟨t, ⟨r, hr, rfl⟩, rfl⟩
    simpa only [parabolicTime_parabolicTimeInv scale hscale] using hr
  · intro hs
    exact ⟨parabolicTimeInv scale origin s, ⟨s, hs, rfl⟩,
      parabolicTime_parabolicTimeInv scale hscale origin s⟩

variable {F : GeneralizedRicciFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {J : SpacetimeInterval}
  {U : TopologicalSpace.Opens C.carrier}

theorem physicalInterval_subset [Nonempty C.carrier]
    (e : GeneralizedFlowCylinder F C origin scale J.domain U) :
    (cylinderPhysicalInterval origin scale e.scale_pos J).domain ⊆ F.interval := by
  rintro _ ⟨s, hs, rfl⟩
  apply (F.slice_nonempty_iff _).mp
  exact ⟨e.forward s hs (Classical.choice (inferInstance : Nonempty C.carrier))⟩

theorem exists_ordinaryFlow
    (e : GeneralizedFlowCylinder F C origin scale J.domain U)
    (hI : (cylinderPhysicalInterval origin scale e.scale_pos J).domain ⊆ F.interval) :
    ∃ G : RicciFlow 3 U J.domain,
      ∀ s (hs : s ∈ J.domain) (x : U) (v w : TangentSpace (𝓡 3) x),
        (G.metric s).inner x v w =
          e.pullbackInner s hs x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w) := by
  let hM12 := generalizedRicciGaugeGeometry_from_M03_M04_M11.{u} 3
  obtain ⟨R⟩ := flowBoxRicciGeometry F (generalizedSpacetimeGeometry 3) hM12
  let K := cylinderPhysicalInterval origin scale e.scale_pos J
  let eR := rawCylinderTransport R.realization e hI
  have hgauges := hM12.gauges F.point Sigma.fst (flowInterval F)
    R.realization.spacetime R.realization.slices R.realization.timeIntervals
    R.realization.gaugeCover R.leafwise
  obtain ⟨H, ⟨W⟩⟩ := hgauges.compatible_realization R.equation U K eR
  obtain ⟨N⟩ := M13.ordinaryParabolicRescaling K W.flow scale e.scale_pos origin
  have hJ := rescale_physicalInterval_domain origin scale e.scale_pos J
  have hsub : J.domain ⊆ (parabolicInterval scale e.scale_pos origin K).domain := by
    rw [hJ]
  let G : RicciFlow 3 U J.domain := Poincare.Geometry.RicciFlow.Harnack.restrictFlow
    N.flow hsub J.ordConnected J.nontrivial
  refine ⟨G, ?_⟩
  intro s hs x v w
  change (N.flow.metric s).inner x v w = _
  rw [N.metric_eq, W.metric_eq]
  change scale * (H.metric (origin + s / scale)).inner x v w = _
  rw [rawCylinderMetric_eq R.realization e hI H ⟨s, hs⟩
    (R.sliceIdentification (origin + s / scale)) x v w]
  exact mul_div_cancel₀ _ e.scale_pos.ne'

end PoincareConjecture.M30.Cylinder
