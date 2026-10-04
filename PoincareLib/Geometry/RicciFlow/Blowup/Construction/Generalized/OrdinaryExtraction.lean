import PoincareLib.Geometry.RicciFlow.Blowup.Construction.SourceNames
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.OrdinaryFlow
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Spacetime.GeneralizedCylinderMetric
import PoincareLib.Geometry.RicciFlow.Rescaling.Construction
import PoincareLib.Geometry.RicciFlow.Harnack.Regularity

/-!
# Ordinary Ricci flow on an open generalized cylinder

Morgan--Tian Definitions 3.38 and 3.40, p. 61, and Corollary 11.3, p. 269.
M12 realizes the supplied raw cylinder in physical time, with its actual
metric. M13 rescales that ordinary flow back to the original cylinder
parameter. The resulting metric is exactly the normalized pullback.
No completeness or compactness conclusion is asserted here.
See the M30 ordinary-extraction derivation for the retained choices and
the endpoint and empty-carrier checks.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M30.Cylinder

open PoincareMT.Proofs.M12

/-- The two affine clocks cancel on the exact interval, preserving either
kind of endpoint (Definition 3.40 and time translation, p. 61). -/
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

/-- A nonempty source carrier forces every physical cylinder time into the
generalized flow's interval, by the total forward map (Definition 3.38,
p. 61). The designated open spatial subset may still be empty. -/
theorem physicalInterval_subset [Nonempty C.carrier]
    (e : GeneralizedFlowCylinder F C origin scale J.domain U) :
    (cylinderPhysicalInterval origin scale e.scale_pos J).domain ⊆ F.interval := by
  rintro _ ⟨s, hs, rfl⟩
  apply (F.slice_nonempty_iff _).mp
  exact ⟨e.forward s hs (Classical.choice (inferInstance : Nonempty C.carrier))⟩

/-- A supplied open cylinder carries an actual ordinary Ricci flow whose
metric is the same normalized pullback (Definition 3.38 and Corollary 11.3,
pp. 61 and 269). Only physical-time containment is assumed; M11, M12 and
M13 supply the geometric realization, equation and parabolic rescaling. -/
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

end PoincareMT.M30.Cylinder
