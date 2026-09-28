import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.BasedEventTransport
import PoincareConjecture.Definitions.M67
import PoincareConjecture.Proofs.M61.ClassAdapters

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem m67_event_based_width_transport
    {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D}
    {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    (B : M59HigherBasepointTransportService)
    (A : RepairedAncestryTransportData D W P K C H B)
    {q : M59SphereQuotient}
    {S : Set.Icc (0 : ℝ) T}
    {s : Set.Icc (0 : ℝ) T}
    {hS : S.1 ∈ D.flow.surgery_times}
    {hpost : Nonempty (D.flow.slice S.1).carrier}
    {hdelta : D.flow.parameters.delta S.1 <
      repairedComparisonDeltaBound D.flow.local_constants}
    {hh : D.flow.parameters.h S.1 <
      repairedComparisonHeightBound D.flow.local_constants}
    {eta : ℝ} (heta : 0 < eta)
    (E : M67EventTransport B A q S s hS hpost hdelta hh eta heta)
    (hM61 : M61WidthTheory.{u} q)
    (hrebased : ∀ (F : ContinuousMap LoopTwoSphere
        (C1FreeLoopSpace (M := (P.component s).carrier.carrier))),
      M61NullFamily F →
      M61Represents q (P.component s).basepoint E.pre.alpha F →
      ∃ G : ContinuousMap LoopTwoSphere
        (C1FreeLoopSpace (M := (H.event_input S hS hpost).child.carrier.carrier)),
        M61NullFamily G ∧
          M61Represents q (H.event_input S hS hpost).child.basepoint
            E.post.alpha G ∧
          G.Homotopic (E.loop.map.comp F)) :
    m61BasedClassWidth q E.post.metric
        (H.event_input S hS hpost).child.basepoint E.post.alpha ≤
      (1 + eta) ^ 2 *
        m61BasedClassWidth q E.pre.metric (P.component s).basepoint E.pre.alpha := by
  let hpre_props : M61BasedClassWidthProperties q E.pre.metric
      (P.component s).basepoint E.pre.alpha :=
    hM61.based_class (M := (P.component s).carrier.carrier) E.pre.metric
      (P.component s).compact
      (P.component s).connected (P.component s).basepoint
      E.pre.pi_two_trivial E.pre.alpha
  let hpost_props : M61BasedClassWidthProperties q E.post.metric
      (H.event_input S hS hpost).child.basepoint E.post.alpha :=
    hM61.based_class
      (M := (H.event_input S hS hpost).child.carrier.carrier) E.post.metric
      (H.event_input S hS hpost).child.compact
      (H.event_input S hS hpost).child.connected
      (H.event_input S hS hpost).child.basepoint E.post.pi_two_trivial
      E.post.alpha
  let hfamily : ∀ F : ContinuousMap LoopTwoSphere
      (C1FreeLoopSpace (M := (P.component s).carrier.carrier)),
      M61NullFamily F → M61FamilyWidthProperties E.pre.metric F := by
    intro F hF
    exact hM61.toM61RawWidthCore.family E.pre.metric
      (P.component s).compact F hF
  let hpostfree : ∀ F : ContinuousMap LoopTwoSphere
      (C1FreeLoopSpace (M := (P.component s).carrier.carrier)),
      M61NullFamily F →
      M61FreeClassWidthProperties E.post.metric (E.loop.map.comp F) := by
    intro F hF
    exact hM61.toM61RawWidthCore.free_class E.post.metric
      (H.event_input S hS hpost).child.compact (E.loop.map.comp F) (by
        intro c
        exact E.null_transport (F c) (hF c))
  exact m67_based_width_transport_of_rebased_family
    (q := q) E.pre.metric E.post.metric (P.component s).basepoint
      (H.event_input S hS hpost).child.basepoint
    E.pre.alpha E.post.alpha E.f E.loop hpre_props hpost_props hfamily hpostfree
    (fun F hF => by
      intro c
      exact E.null_transport (F c) (hF c))
    hrebased eta heta (fun _F _hF => E.filling_transport)

theorem m67_event_based_width_transport_of_represented_family
    {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D}
    {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    (B : M59HigherBasepointTransportService)
    (A : RepairedAncestryTransportData D W P K C H B)
    (Syst : M59IdentificationSystem.{u})
    {S : Set.Icc (0 : ℝ) T}
    {s : Set.Icc (0 : ℝ) T}
    {hS : S.1 ∈ D.flow.surgery_times}
    {hpost : Nonempty (D.flow.slice S.1).carrier}
    {hdelta : D.flow.parameters.delta S.1 <
      repairedComparisonDeltaBound D.flow.local_constants}
    {hh : D.flow.parameters.h S.1 <
      repairedComparisonHeightBound D.flow.local_constants}
    {eta : ℝ} (heta : 0 < eta)
    (E : M67EventTransport B A Syst.quotient S s hS hpost hdelta hh eta heta)
    (hM61 : M61WidthTheory.{u} Syst.quotient)
    (hrepresented : ∀ (F : ContinuousMap LoopTwoSphere
        (C1FreeLoopSpace (M := (P.component s).carrier.carrier))),
      M61NullFamily F →
      M61Represents Syst.quotient (P.component s).basepoint E.pre.alpha F →
      M61Represents Syst.quotient
        (H.event_input S hS hpost).child.basepoint E.post.alpha
        (E.loop.map.comp F)) :
    m61BasedClassWidth Syst.quotient E.post.metric
        (H.event_input S hS hpost).child.basepoint E.post.alpha ≤
      (1 + eta) ^ 2 *
        m61BasedClassWidth Syst.quotient E.pre.metric
          (P.component s).basepoint E.pre.alpha := by
  apply m67_event_based_width_transport B A heta E hM61
  intro F hF hFrep
  refine ⟨E.post.family, E.post.family_null, E.post.represents, ?_⟩
  exact (m61Represents_iff_homotopic
    (Syst.core (H.event_input S hS hpost).child.compact
      (H.event_input S hS hpost).child.connected
      (H.event_input S hS hpost).child.basepoint E.post.pi_two_trivial)
    E.post.represents (E.loop.map.comp F)).mp (hrepresented F hF hFrep)

theorem m67_event_based_width_transport_of_event
    {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D}
    {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    (B : M59HigherBasepointTransportService)
    (A : RepairedAncestryTransportData D W P K C H B)
    (Syst : M59IdentificationSystem.{u})
    {S : Set.Icc (0 : ℝ) T}
    {s : Set.Icc (0 : ℝ) T}
    {hS : S.1 ∈ D.flow.surgery_times}
    {hpost : Nonempty (D.flow.slice S.1).carrier}
    {hdelta : D.flow.parameters.delta S.1 <
      repairedComparisonDeltaBound D.flow.local_constants}
    {hh : D.flow.parameters.h S.1 <
      repairedComparisonHeightBound D.flow.local_constants}
    {eta : ℝ} (heta : 0 < eta)
    (E : M67EventTransport B A Syst.quotient S s hS hpost hdelta hh eta heta)
    (hM61 : M61WidthTheory.{u} Syst.quotient) :
    m61BasedClassWidth Syst.quotient E.post.metric
        (H.event_input S hS hpost).child.basepoint E.post.alpha ≤
      (1 + eta) ^ 2 *
        m61BasedClassWidth Syst.quotient E.pre.metric
          (P.component s).basepoint E.pre.alpha := by
  exact m67_event_based_width_transport_of_represented_family B A Syst heta E
    hM61 E.represents_transport

end PoincareConjecture
