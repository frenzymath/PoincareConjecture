import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Assembly.ClassPath.SelectedEvent
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Extinction.Width.Transport.Assembly.ClassPath.Regular

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {W : RepairedEventChildWitness D.flow} {T : ℝ}
  {P : RepairedComponentPath D.flow T W}
  {K : RepairedComparisonMapData D} {C : RepairedComparisonHomotopyData D K}

structure M67ClassPath
    (H : RepairedAncestryTransportInput D W P K C)
    (B : M59HigherBasepointTransportService.{u})
    (A : RepairedAncestryTransportData D W P K C H B)
    (S : M59IdentificationSystem.{u})
    (initial : M67InitialClassData S (P.component (m67InitialTime P)) (D.flow.metric 0)) where
  datum : ∀ t : Set.Icc (0 : ℝ) T, M67ClassDatum S (P.component t)
  initial_eq : datum (m67InitialTime P) = initial.toClassDatum
  regular_transport : ∀ (a b : Set.Icc (0 : ℝ) T) (hab : a.1 < b.1)
      (hJ : Disjoint D.flow.surgery_times (Set.Ioc a.1 b.1)),
    M67AlphaTransport B (P.component a).basepoint (P.component b).basepoint
      (repairedDiffeomorphContinuousMap (P.regular_transport a b hab hJ))
      (datum a).alpha (datum b).alpha
  event_eq : ∀ (t : Set.Icc (0 : ℝ) T) (ht : t.1 ∈ D.flow.surgery_times)
      (hpost : Nonempty (D.flow.slice t.1).carrier)
      (hdelta : D.flow.parameters.delta t.1 < repairedComparisonDeltaBound D.flow.local_constants)
      (hh : D.flow.parameters.h t.1 < repairedComparisonHeightBound D.flow.local_constants),
    datum t = m67SelectedEventClassDatum H B A S t ht hpost hdelta hh
      (datum (m67EventPreTime t ht hpost))

theorem m67_class_path_exists
    (H : RepairedAncestryTransportInput D W P K C)
    (B : M59HigherBasepointTransportService.{u})
    (A : RepairedAncestryTransportData D W P K C H B)
    (S : M59IdentificationSystem.{u})
    (initial : M67InitialClassData S (P.component (m67InitialTime P)) (D.flow.metric 0))
    (hcomparison : M67EventComparisonBounds D.flow (Set.Icc 0 T)) :
    Nonempty (M67ClassPath H B A S initial) := by
  classical
  let events : Finset (Set.Icc (0 : ℝ) T) := P.surgery_times.subtype (· ∈ Set.Icc 0 T)
  have hevents (t : Set.Icc (0 : ℝ) T) : t ∈ events ↔ t.1 ∈ D.flow.surgery_times := by
    change t ∈ P.surgery_times.subtype (· ∈ Set.Icc 0 T) ↔ _
    rw [Finset.mem_subtype]
    change t.1 ∈ (↑P.surgery_times : Set ℝ) ↔ _
    rw [P.surgery_times_eq]
    exact and_iff_left t.property
  have hpost (t : Set.Icc (0 : ℝ) T) : Nonempty (D.flow.slice t.1).carrier :=
    ⟨(P.component t).inclusion (P.component t).basepoint⟩
  let before (t : Set.Icc (0 : ℝ) T) (ht : t ∈ events) :=
    m67EventPreTime t ((hevents t).mp ht) (hpost t)
  have hbefore (t : Set.Icc (0 : ℝ) T) (ht : t ∈ events) : before t ht < t :=
    (D.flow.event t.1 ((hevents t).mp ht)).tMinus_lt
  have hzero : m67InitialTime P ∉ events :=
    fun h => D.flow.zero_not_surgery ((hevents (m67InitialTime P)).mp h)
  let event (t : Set.Icc (0 : ℝ) T) (ht : t ∈ events) :
      M67ClassDatum S (P.component (before t ht)) → M67ClassDatum S (P.component t) :=
    m67SelectedEventClassDatum H B A S t ((hevents t).mp ht) (hpost t)
      (hcomparison t.1 t.property ((hevents t).mp ht)).1
      (hcomparison t.1 t.property ((hevents t).mp ht)).2
  obtain ⟨sol, hinitial, hregular, hevent⟩ := m67_finite_transport_section
    (m67InitialTime P) (fun t => t.property.1) events hzero before hbefore
    (fun t => M67ClassDatum S (P.component t)) initial.toClassDatum
    (m67OrdinaryClassDatum H S B hevents)
    (m67OrdinaryClassDatum_refl H S B hevents)
    (m67OrdinaryClassDatum_trans H S B hevents) event
  refine ⟨{ datum := sol
            initial_eq := hinitial
            regular_transport := ?_
            event_eq := ?_ }⟩
  · intro a b hab hJ
    have hordinary : M67OrdinaryBetween events a b := by
      refine ⟨hab.le, Set.disjoint_left.mpr ?_⟩
      intro t ht htab
      exact Set.disjoint_left.mp hJ ((hevents t).mp ht) htab
    have hdatum : m67RegularClassDatum H S B a b hab hJ (sol a) = sol b := by
      have hh := hregular a b hordinary
      change m67RegularClassDatumLE H S B a b hab.le _ (sol a) = sol b at hh
      rw [m67RegularClassDatumLE_of_lt H S B a b hab] at hh
      exact hh
    exact hdatum ▸ m67RegularClassDatum_transport H S B a b hab hJ (sol a)
  · intro t ht hp hd hh
    exact hevent t ((hevents t).mpr ht)

variable {H : RepairedAncestryTransportInput D W P K C}
  {B : M59HigherBasepointTransportService.{u}}
  {A : RepairedAncestryTransportData D W P K C H B}
  {S : M59IdentificationSystem.{u}}
  {initial : M67InitialClassData S (P.component (m67InitialTime P)) (D.flow.metric 0)}

theorem M67ClassPath.event_post_alpha_heq
    (X : M67ClassPath H B A S initial)
    (t : Set.Icc (0 : ℝ) T) (ht : t.1 ∈ D.flow.surgery_times)
    (hpost : Nonempty (D.flow.slice t.1).carrier)
    (hdelta : D.flow.parameters.delta t.1 < repairedComparisonDeltaBound D.flow.local_constants)
    (hh : D.flow.parameters.h t.1 < repairedComparisonHeightBound D.flow.local_constants) :
    HEq (m67EventPostClassDatum H B A S t ht hpost hdelta hh
      (X.datum (m67EventPreTime t ht hpost))).alpha (X.datum t).alpha := by
  rw [X.event_eq t ht hpost hdelta hh]
  exact (M67ClassDatum.cast_alpha_heq _ _).symm

theorem M67ClassPath.event_approximant_transport
    (X : M67ClassPath H B A S initial)
    (t : Set.Icc (0 : ℝ) T) (ht : t.1 ∈ D.flow.surgery_times)
    (hpost : Nonempty (D.flow.slice t.1).carrier)
    (hdelta : D.flow.parameters.delta t.1 < repairedComparisonDeltaBound D.flow.local_constants)
    (hh : D.flow.parameters.h t.1 < repairedComparisonHeightBound D.flow.local_constants)
    (s : Set.Icc (0 : ℝ) T)
    (hs : (D.flow.event t.1 ht).tMinus < s.1)
    (hJ : Disjoint D.flow.surgery_times (Set.Ioc (D.flow.event t.1 ht).tMinus s.1))
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
      (X.datum s).alpha
      (m67EventPostClassDatum H B A S t ht hpost hdelta hh
        (X.datum (m67EventPreTime t ht hpost))).alpha :=
  m67_event_class_transport_of_regular H B A S t ht hpost hdelta hh
    (X.datum (m67EventPreTime t ht hpost)) s hs hJ (X.datum s)
    (X.regular_transport _ _ hs hJ) f hsmooth hbase hmap

end PoincareConjecture
