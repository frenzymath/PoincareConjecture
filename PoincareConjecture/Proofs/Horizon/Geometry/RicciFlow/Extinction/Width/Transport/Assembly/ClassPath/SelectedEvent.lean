import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Assembly.ClassPath.Event
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Event.Parent

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

def M67ClassDatum.cast {S : M59IdentificationSystem.{u}}
    {U : GeneralizedSliceCarrier.{u}} {C₁ C₂ : SurgerySelectedComponent U}
    (h : C₁ = C₂) (x : M67ClassDatum S C₁) : M67ClassDatum S C₂ := h ▸ x

theorem M67ClassDatum.cast_alpha_heq {S : M59IdentificationSystem.{u}}
    {U : GeneralizedSliceCarrier.{u}} {C₁ C₂ : SurgerySelectedComponent U}
    (h : C₁ = C₂) (x : M67ClassDatum S C₁) :
    HEq (x.cast h).alpha x.alpha := by subst C₂; rfl

theorem M67ClassDatum.cast_transport {S : M59IdentificationSystem.{u}}
    (B : M59HigherBasepointTransportService.{u})
    {U : GeneralizedSliceCarrier.{u}} {C₁ C₂ : SurgerySelectedComponent U}
    (h : C₂ = C₁) (x : M67ClassDatum S C₁) :
    M67AlphaTransport B C₁.basepoint C₂.basepoint
      (repairedDiffeomorphContinuousMap (m67ComponentIdentification C₁ C₂ h))
      x.alpha (x.cast h.symm).alpha := by
  subst C₂
  exact m67_alpha_transport_refl B C₁.basepoint x.alpha

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {W : RepairedEventChildWitness D.flow} {T : ℝ}
  {P : RepairedComponentPath D.flow T W}
  {K : RepairedComparisonMapData D} {C : RepairedComparisonHomotopyData D K}
  (H : RepairedAncestryTransportInput D W P K C)
  (B : M59HigherBasepointTransportService.{u})
  (A : RepairedAncestryTransportData D W P K C H B)
  (S : M59IdentificationSystem.{u})
  (t : Set.Icc (0 : ℝ) T) (ht : t.1 ∈ D.flow.surgery_times)
  (hpost : Nonempty (D.flow.slice t.1).carrier)
  (hdelta : D.flow.parameters.delta t.1 < repairedComparisonDeltaBound D.flow.local_constants)
  (hh : D.flow.parameters.h t.1 < repairedComparisonHeightBound D.flow.local_constants)

def m67EventParentClassDatum
    (x : M67ClassDatum S (P.component (m67EventPreTime t ht hpost))) :
    M67ClassDatum S (H.event_input t ht hpost).parent :=
  x.cast (eq_of_heq (H.event_parent_path t ht hpost)).symm

noncomputable def m67EventPostClassDatum
    (x : M67ClassDatum S (P.component (m67EventPreTime t ht hpost))) :
    M67ClassDatum S (H.event_input t ht hpost).child :=
  m67EventClassDatum S B (H.event_input t ht hpost)
    (A.event_output t ht hpost hdelta hh) (m67EventParentClassDatum H S t ht hpost x)

noncomputable def m67SelectedEventClassDatum
    (x : M67ClassDatum S (P.component (m67EventPreTime t ht hpost))) :
    M67ClassDatum S (P.component t) :=
  (m67EventPostClassDatum H B A S t ht hpost hdelta hh x).cast
    (eq_of_heq (H.event_child_path t ht hpost))

theorem m67_event_class_transport_of_regular
    (x : M67ClassDatum S (P.component (m67EventPreTime t ht hpost)))
    (s : Set.Icc (0 : ℝ) T)
    (hs : (D.flow.event t.1 ht).tMinus < s.1)
    (hJ : Disjoint D.flow.surgery_times (Set.Ioc (D.flow.event t.1 ht).tMinus s.1))
    (y : M67ClassDatum S (P.component s))
    (hregular : M67AlphaTransport B
      (P.component (m67EventPreTime t ht hpost)).basepoint (P.component s).basepoint
      (repairedDiffeomorphContinuousMap
        (P.regular_transport (m67EventPreTime t ht hpost) s hs hJ)) x.alpha y.alpha)
    (f : C((H.event_input t ht hpost).parent.carrier.carrier,
      (H.event_input t ht hpost).child.carrier.carrier))
    (hsmooth : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (hbase : f (H.event_input t ht hpost).parent.basepoint =
      (A.event_output t ht hpost hdelta hh).comparison.target_basepoint)
    (hmap : ∀ alpha, surgeryHomotopyMap (n := 3) f hbase alpha =
      surgeryHomotopyMap (A.event_output t ht hpost hdelta hh).comparison.map
        (A.event_output t ht hpost hdelta hh).comparison.based alpha) :
    M67AlphaTransport B (P.component s).basepoint
      (H.event_input t ht hpost).child.basepoint
      (f.comp (repairedDiffeomorphContinuousMap
        (m67EventPreToParent H t ht hpost s hs hJ)))
      y.alpha (m67EventPostClassDatum H B A S t ht hpost hdelta hh x).alpha := by
  have hback := m67_alpha_transport_symm S B
    (P.regular_transport (m67EventPreTime t ht hpost) s hs hJ)
    (S.core (P.component (m67EventPreTime t ht hpost)).compact
      (P.component (m67EventPreTime t ht hpost)).connected
      (P.component (m67EventPreTime t ht hpost)).basepoint x.pi_two_trivial) hregular
  have hparent := x.cast_transport B (eq_of_heq (H.event_parent_path t ht hpost))
  have hevent := m67EventClassDatum_transport S B (H.event_input t ht hpost)
    (A.event_output t ht hpost hdelta hh) (m67EventParentClassDatum H S t ht hpost x)
    f hsmooth hbase hmap
  exact m67_alpha_transport_trans B (m67_alpha_transport_trans B hback hparent) hevent

end PoincareConjecture
