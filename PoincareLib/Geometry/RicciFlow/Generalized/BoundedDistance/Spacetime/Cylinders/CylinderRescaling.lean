import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.SourceNames
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Spacetime.Cylinders.CylinderFlow
import PoincareLib.Geometry.RicciFlow.Rescaling.Construction

/-!
# Ordinary parabolic rescaling on a generalized-flow cylinder

The M12 raw-cylinder witness is an ordinary Ricci flow on the physical
clock.  M13 then supplies the exact affine-clock rescaling, retaining the
same open source carrier and producing an actual normalized ordinary flow.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M28

variable {F : GeneralizedRicciFlowData.{u}}
  {C : GeneralizedSliceCarrier.{u}} {a q : ℝ} {J : SpacetimeInterval}
  {U : TopologicalSpace.Opens C.carrier}
  (e : GeneralizedFlowCylinder F C a q J.domain U)
  (hI : (Proofs.M12.cylinderPhysicalInterval a q e.scale_pos J).domain ⊆ F.interval)

/-- The physical ordinary witness and its M13 parabolic rescaling, bundled
so downstream arguments can use the selected metric and flow directly. -/
structure RescaledRawCylinderData where
  geometry : Proofs.M12.FlowBoxRicciGeometry F
  metric : SpacetimeCylinderMetric
    (Proofs.M12.rawCylinderTransport geometry.realization e hI)
  ordinary : OrdinaryGaugeWitness geometry.leafwise
    (Proofs.M12.rawCylinderTransport geometry.realization e hI) metric
  rescaling : OrdinaryParabolicRescaling ordinary.flow q e.scale_pos a

/-- M12's compatible-cylinder construction followed by M13's ordinary
parabolic rescaling gives an actual normalized flow on the affine image of
the physical cylinder interval. -/
theorem exists_rescaled_raw_cylinder_flow :
    Nonempty (RescaledRawCylinderData e hI) := by
  obtain ⟨G, K, ⟨W⟩⟩ := exists_raw_cylinder_ordinary_flow e hI
  obtain ⟨P⟩ := M13.ordinaryParabolicRescaling _ W.flow q e.scale_pos a
  exact ⟨{
    geometry := G
    metric := K
    ordinary := W
    rescaling := P
  }⟩

/-- The normalized flow metric is exactly the positive scale factor times the
physical raw-cylinder metric at the inverse affine time. -/
theorem rescaled_metric_eq
    (H : RescaledRawCylinderData e hI) (s : ℝ)
    (x : U) (v w : TangentSpace (𝓡 3) x) :
    (H.rescaling.flow.metric s).inner x v w =
      q * (H.ordinary.flow.metric (parabolicTimeInv q a s)).inner x v w := by
  exact H.rescaling.metric_eq s x v w

noncomputable def rescaledTime
    (s : (parabolicInterval q e.scale_pos a
      (Proofs.M12.cylinderPhysicalInterval a q e.scale_pos J)).domain) : J.domain :=
  Proofs.M12.cylinderClockHomeomorph a q e.scale_pos J
    ⟨parabolicTimeInv q a s.val,
      (mem_parabolicInterval_iff q e.scale_pos a
        (Proofs.M12.cylinderPhysicalInterval a q e.scale_pos J) s.val).1 s.property⟩

@[simp] theorem rescaledTime_val
    (s : (parabolicInterval q e.scale_pos a
      (Proofs.M12.cylinderPhysicalInterval a q e.scale_pos J)).domain) :
    (rescaledTime e s).val = s.val := by
  unfold rescaledTime
  dsimp [Proofs.M12.cylinderClockHomeomorph]
  exact parabolicTime_parabolicTimeInv q e.scale_pos a s.val

/-- After rebasing the target clock through the original cylinder interval,
the normalized flow metric is the cylinder pullback metric itself. -/
theorem rescaled_pullback_metric_eq
    (H : RescaledRawCylinderData e hI)
    (s : (parabolicInterval q e.scale_pos a
      (Proofs.M12.cylinderPhysicalInterval a q e.scale_pos J)).domain)
    (x : U) (v w : TangentSpace (𝓡 3) x) :
    (H.rescaling.flow.metric s.val).inner x v w =
      e.pullbackInner (rescaledTime e s).val (rescaledTime e s).property x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w) := by
  let K := Proofs.M12.cylinderPhysicalInterval a q e.scale_pos J
  let t : K.domain :=
    ⟨parabolicTimeInv q a s.val,
      (mem_parabolicInterval_iff q e.scale_pos a K s.val).1 s.property⟩
  let sJ : J.domain := rescaledTime e s
  have hsJ : sJ.val = s.val := rescaledTime_val e s
  have ht : t.val = a + sJ.val / q := by
    calc
      t.val = parabolicTimeInv q a s.val := rfl
      _ = a + s.val / q := by rfl
      _ = a + sJ.val / q := by rw [hsJ]
  calc
    (H.rescaling.flow.metric s.val).inner x v w =
        q * (H.ordinary.flow.metric (parabolicTimeInv q a s.val)).inner x v w :=
      H.rescaling.metric_eq s.val x v w
    _ = q * (H.metric.metric (parabolicTimeInv q a s.val)).inner x v w := by
      rw [H.ordinary.metric_eq]
    _ = q * (H.metric.metric t.val).inner x v w := by rfl
    _ = q * (e.pullbackInner sJ.val sJ.property x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w) / q) := by
      rw [ht]
      rw [Proofs.M12.rawCylinderMetric_eq H.geometry.realization e hI H.metric sJ
        (H.geometry.sliceIdentification (a + sJ.val / q)) x v w]
    _ = e.pullbackInner sJ.val sJ.property x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w) := by
      field_simp [ne_of_gt e.scale_pos]

end PoincareMT.M28
