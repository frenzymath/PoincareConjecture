import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Class.Regular
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Class.Uniqueness
import PoincareConjecture.Definitions.M67InitialClass

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology unitInterval

universe u

namespace PoincareConjecture

structure M67ClassDatum (S : M59IdentificationSystem.{u})
    {A : GeneralizedSliceCarrier.{u}} (C : SurgerySelectedComponent A) where
  pi_two_trivial : Subsingleton (HomotopyGroup.Pi 2 C.carrier.carrier C.basepoint)
  alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := C.carrier.carrier))
    (constantC1Loop C.basepoint)
  nonzero : (S.core C.compact C.connected C.basepoint pi_two_trivial).pi_two_pi_three
    alpha ≠ 1

@[ext] theorem M67ClassDatum.ext
    {S : M59IdentificationSystem.{u}}
    {A : GeneralizedSliceCarrier.{u}} {C : SurgerySelectedComponent A}
    {a b : M67ClassDatum S C} (h : a.alpha = b.alpha) : a = b := by
  cases a
  cases b
  cases h
  rfl

def M67InitialClassData.toClassDatum
    {S : M59IdentificationSystem.{u}} {A : GeneralizedSliceCarrier.{u}}
    {C : SurgerySelectedComponent A} {g : RiemannianMetric 3 A.carrier}
    (initial : M67InitialClassData S C g) : M67ClassDatum S C :=
  ⟨initial.pi_two_trivial, initial.alpha, initial.nonzero⟩

theorem m67_class_datum_regular_exists
    {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow} {T : ℝ}
    {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D} {C : RepairedComparisonHomotopyData D K}
    (H : RepairedAncestryTransportInput D W P K C)
    (S : M59IdentificationSystem.{u}) (B : M59HigherBasepointTransportService.{u})
    (a b : Set.Icc (0 : ℝ) T) (hab : a.1 < b.1)
    (hJ : Disjoint D.flow.surgery_times (Set.Ioc a.1 b.1))
    (x : M67ClassDatum S (P.component a)) :
    ∃ y : M67ClassDatum S (P.component b),
      M67AlphaTransport B (P.component a).basepoint (P.component b).basepoint
        (repairedDiffeomorphContinuousMap (P.regular_transport a b hab hJ))
        x.alpha y.alpha := by
  obtain ⟨p⟩ := H.regular_basepoint_bridge a b hab hJ
  obtain ⟨hpi, alpha, hnonzero, htransport⟩ := m67_alpha_transport_of_diffeomorph
    S B (P.component a).compact (P.component a).connected
    (P.component b).compact (P.component b).connected
    (P.component a).basepoint (P.component b).basepoint
    (P.regular_transport a b hab hJ) p (m67ConstantLoopPath p)
    x.pi_two_trivial x.alpha x.nonzero
  exact ⟨⟨hpi, alpha, hnonzero⟩, htransport⟩

noncomputable def m67RegularClassDatum
    {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow} {T : ℝ}
    {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D} {C : RepairedComparisonHomotopyData D K}
    (H : RepairedAncestryTransportInput D W P K C)
    (S : M59IdentificationSystem.{u}) (B : M59HigherBasepointTransportService.{u})
    (a b : Set.Icc (0 : ℝ) T) (hab : a.1 < b.1)
    (hJ : Disjoint D.flow.surgery_times (Set.Ioc a.1 b.1))
    (x : M67ClassDatum S (P.component a)) : M67ClassDatum S (P.component b) :=
  (m67_class_datum_regular_exists H S B a b hab hJ x).choose

theorem m67RegularClassDatum_transport
    {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow} {T : ℝ}
    {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D} {C : RepairedComparisonHomotopyData D K}
    (H : RepairedAncestryTransportInput D W P K C)
    (S : M59IdentificationSystem.{u}) (B : M59HigherBasepointTransportService.{u})
    (a b : Set.Icc (0 : ℝ) T) (hab : a.1 < b.1)
    (hJ : Disjoint D.flow.surgery_times (Set.Ioc a.1 b.1))
    (x : M67ClassDatum S (P.component a)) :
    M67AlphaTransport B (P.component a).basepoint (P.component b).basepoint
      (repairedDiffeomorphContinuousMap (P.regular_transport a b hab hJ))
      x.alpha (m67RegularClassDatum H S B a b hab hJ x).alpha :=
  (m67_class_datum_regular_exists H S B a b hab hJ x).choose_spec

end PoincareConjecture
