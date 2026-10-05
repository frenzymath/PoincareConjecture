import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.History.RegularCylinderTransport
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.History.Transport.GuardedCylinders

/-!
# The actual surgery cylinder on the retained spacetime

Apply M33's guarded conversion once. Its actual map and metric identities
then pass through the already selected regular-history realization.
No whole-slice distance identity at a surgery time is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M48RegularSpacetimeData

open EpochExtension.Spacetime

variable {F : SurgeryFlowData.{u}} {T : ℝ} {L : RepairedPreterminalSlab F T}
  (R : M48RegularSpacetimeData L) {C : GeneralizedSliceCarrier.{u}}
  {a q : ℝ} {J : SpacetimeInterval} {U : TopologicalSpace.Opens C.carrier}
  (e : SurgeryFlowCylinder F C a q J.domain U)
  (htime : ∀ s ∈ J.domain, a + s / q ∈ R.history.generalized.interval)
  (hregular : ∀ s hs, e.forward s hs '' (U : Set C.carrier) ⊆
    m33RegularRegion F (a + s / q))

noncomputable def surgeryCylinder :
    GeneralizedFlowCylinder R.history.generalized C a q J.domain U :=
  Classical.choose (R.history.cylinders_from_surgery C a q J.domain U
    U.isOpen htime e hregular)

theorem surgeryCylinder_forward (s : ℝ) (hs : s ∈ J.domain) (x : C.carrier)
    (hx : x ∈ U) :
    R.history.history.forward (a + s / q) (htime s hs)
      ((R.surgeryCylinder e htime hregular).forward s hs x) = e.forward s hs x :=
  (Classical.choose_spec (R.history.cylinders_from_surgery C a q J.domain U
    U.isOpen htime e hregular)).1 s hs x hx

theorem surgeryCylinder_pullback (s : ℝ) (hs : s ∈ J.domain) (x : C.carrier)
    (hx : x ∈ U) (v w : TangentSpace (𝓡 3) x) :
    (R.surgeryCylinder e htime hregular).pullbackInner s hs x v w =
      e.pullbackInner s hs x v w :=
  (Classical.choose_spec (R.history.cylinders_from_surgery C a q J.domain U
    U.isOpen htime e hregular)).2 s hs x hx v w

theorem surgeryCylinder_time_subset :
    (cylinderPhysicalInterval a q (R.surgeryCylinder e htime hregular).scale_pos J).domain ⊆
      R.history.generalized.interval := by
  rintro _ ⟨s, hs, rfl⟩
  exact htime s hs

noncomputable def surgerySpacetimeCylinder :
    CompatibleSpacetimeCylinder R.geometry.realization.spacetime
      (R.geometry.realization.timeIntervals.interval
        (cylinderPhysicalInterval a q e.scale_pos J)) U :=
  R.regularCylinder (R.surgeryCylinder e htime hregular)
    (R.surgeryCylinder_time_subset e htime hregular)

noncomputable def surgerySpacetimeCylinderMetric :
    SpacetimeCylinderMetric (R.surgerySpacetimeCylinder e htime hregular) :=
  R.regularCylinderMetric (R.surgeryCylinder e htime hregular)
    (R.surgeryCylinder_time_subset e htime hregular)

theorem surgerySpacetimeCylinder_metric (s : J.domain) (x : U)
    (v w : TangentSpace (𝓡 3) x) :
    ((R.surgerySpacetimeCylinderMetric e htime hregular).metric (a + s.val / q)).inner x v w =
      e.pullbackInner s.val s.property x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w) / q := by
  have h := R.regularCylinder_metric (R.surgeryCylinder e htime hregular)
    (R.surgeryCylinder_time_subset e htime hregular) s x v w
  rw [R.surgeryCylinder_pullback e htime hregular s.val s.property x.val x.property] at h
  exact h

end PoincareMT.M48RegularSpacetimeData
