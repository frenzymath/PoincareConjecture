import PoincareConjecture.Definitions.Ch15.SurgeryTopology
import PoincareConjecture.Definitions.Ch18.FiniteExtinction
import PoincareConjecture.Definitions.Ch17.GlobalSurgery
import PoincareConjecture.Definitions.M52GlobalFlow
import PoincareConjecture.Definitions.M38LocalTopology
import PoincareConjecture.Definitions.M72TopologyTransport

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

structure M72EventTopologyData (F : SurgeryFlowData.{u})
    (T : ℝ) (hT : T ∈ F.surgery_times) where

  pre_time : ℝ
  pre_time_nonnegative : 0 ≤ pre_time
  pre_time_lt : pre_time < T
  conclusion : SurgeryTopologyConclusion (F.slice pre_time) (F.slice T)

  nonempty_reference : ∀ hN : Nonempty (F.slice T).carrier,
    (@F.event T hT hN).tMinus < pre_time
  vanishing_reference : ∀ hE : IsEmpty (F.slice T).carrier,
    (@F.vanishing_event T hT hE).tMinus < pre_time

  cap_correspondence :
    ∀ hN : Nonempty (F.slice T).carrier,
      ∀ i : Fin (@F.event T hT hN).cap_count,
        ∃ j : Fin conclusion.piece_count,
          conclusion.kind j = .survivor ∧
          Set.Subset ((@F.event T hT hN).caps i).carrier
            (conclusion.survivor_region j)

  no_survivor_if_empty :
    ∀ _hE : IsEmpty (F.slice T).carrier,
      ∀ i : Fin conclusion.piece_count,
        conclusion.kind i ≠ .survivor

  predecessor : ℝ
  predecessor_anchor : predecessor = 0 ∨ predecessor ∈ F.surgery_times
  predecessor_lt : predecessor < pre_time
  no_surgery_before :
    Disjoint F.surgery_times (Set.Ioc predecessor pre_time)
  no_surgery_after :
    Disjoint F.surgery_times (Set.Ioo pre_time T)
  predecessor_time_domain :
    Set.Icc predecessor pre_time ⊆ F.time_domain
  predecessor_transport :
    Diffeomorph (𝓡 3) (𝓡 3)
      (F.slice predecessor).carrier (F.slice pre_time).carrier ∞
  predecessor_transport_eq_regular :
    ∀ x, predecessor_transport x =
      (F.regular_slabs predecessor pre_time predecessor_lt
        predecessor_time_domain no_surgery_before).identify
        ⟨pre_time, ⟨predecessor_lt.le, le_rfl⟩⟩ x

def M72EventTopologyData.nonemptyReferenceMap
    {F : SurgeryFlowData.{u}} {T : ℝ} {hT : T ∈ F.surgery_times}
    (E : M72EventTopologyData F T hT) [hN : Nonempty (F.slice T).carrier] :
    Diffeomorph (𝓡 3) (𝓡 3)
      (F.slice (F.event T hT).tMinus).carrier (F.slice E.pre_time).carrier ∞ :=
  (F.event T hT).pre_identify
    ⟨E.pre_time, ⟨(E.nonempty_reference hN).le, E.pre_time_lt⟩⟩

def M72EventTopologyData.vanishingReferenceMap
    {F : SurgeryFlowData.{u}} {T : ℝ} {hT : T ∈ F.surgery_times}
    (E : M72EventTopologyData F T hT) [hE : IsEmpty (F.slice T).carrier] :
    Diffeomorph (𝓡 3) (𝓡 3)
      (F.slice (F.vanishing_event T hT).tMinus).carrier (F.slice E.pre_time).carrier ∞ :=
  (F.vanishing_event T hT).pre_identify
    ⟨E.pre_time, ⟨(E.vanishing_reference hE).le, E.pre_time_lt⟩⟩

structure M72ComponentAssemblyTransport
    (P Q : GeneralizedSliceCarrier.{u}) where
  region : Set Q.carrier
  component_equivalence : SurgeryRegionEquivalence P Q Set.univ region

structure M72SuccessorTransport (F : SurgeryFlowData.{u})
    (H T T' : ℝ) (hT : T ∈ F.surgery_times) (hT' : T' ∈ F.surgery_times)
    (E : M72EventTopologyData F T hT)
    (E' : M72EventTopologyData F T' hT')
    (i : Fin E.conclusion.piece_count) where
  order : T < T'
  target_horizon : T' ≤ H
  next_minimal : ∀ T'' : ℝ, T < T'' → T'' ∈ F.surgery_times → T' ≤ T''
  next_predecessor : E'.predecessor = T
  pre_after : T < E'.pre_time
  time_domain : Set.Icc T E'.pre_time ⊆ F.time_domain
  no_surgery : Disjoint F.surgery_times (Set.Ioc T E'.pre_time)
  transport : Diffeomorph (𝓡 3) (𝓡 3)
    (F.slice T).carrier (F.slice E'.pre_time).carrier ∞
  transport_eq_regular : ∀ x,
    transport x = (F.regular_slabs T E'.pre_time pre_after time_domain no_surgery).identify
      ⟨E'.pre_time, ⟨pre_after.le, le_rfl⟩⟩ x
  component_point : (F.slice E'.pre_time).carrier
  survivor_image : Set.image transport (E.conclusion.survivor_region i) =
    connectedComponent component_point

structure M72SuccessorChoice (F : SurgeryFlowData.{u})
    (H : ℝ)
    (event : ∀ (T : ℝ) (hT : T ∈ F.surgery_times), T ≤ H →
      M72EventTopologyData F T hT)
    (T : ℝ) (hT : T ∈ F.surgery_times)
    (E : M72EventTopologyData F T hT)
    (i : Fin E.conclusion.piece_count) where
  target_time : ℝ
  target_mem : target_time ∈ F.surgery_times
  target_before : target_time ≤ H
  successor : M72SuccessorTransport F H T target_time hT target_mem E
    (event target_time target_mem target_before) i

def M72SuccessorChoice.target_event
    {F : SurgeryFlowData.{u}} {H : ℝ}
    {event : ∀ (T : ℝ) (hT : T ∈ F.surgery_times), T ≤ H →
      M72EventTopologyData F T hT}
    {T : ℝ} {hT : T ∈ F.surgery_times}
    {E : M72EventTopologyData F T hT} {i : Fin E.conclusion.piece_count}
    (S : M72SuccessorChoice F H event T hT E i) :
    M72EventTopologyData F S.target_time S.target_mem :=
  event S.target_time S.target_mem S.target_before

structure M72LocalTopologyService (F : SurgeryFlowData.{u}) (H : ℝ) where

  admissible : SurgeryFlowAdmissible F
  m38_data : RawLocalSurgeryTopologyData F
  event : ∀ (T : ℝ) (hT : T ∈ F.surgery_times) (_hH : T ≤ H),
    M72EventTopologyData F T hT

  m38_nonempty_source : ∀ (T : ℝ) (hT : T ∈ F.surgery_times)
    (_hH : T ≤ H) (_hN : Nonempty (F.slice T).carrier),
    letI := _hN
    (event T hT _hH).conclusion =
      (Classical.choice (m38_data.nonempty_reconstruction T hT)).conclusion.transportPre
        (event T hT _hH).nonemptyReferenceMap
  m38_vanishing_source : ∀ (T : ℝ) (hT : T ∈ F.surgery_times)
    (_hH : T ≤ H) (_hE : IsEmpty (F.slice T).carrier),
    letI := _hE
    (event T hT _hH).conclusion =
      (Classical.choice (m38_data.vanishing_reconstruction T hT)).conclusion.transportPre
        (event T hT _hH).vanishingReferenceMap

structure M72ReconstructionInput
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    (N : NormalizedInitialMetric (M := M)) where

  global : RepairedGlobalFlowData N
  extinction : FiniteExtinctionConclusion global.certificate.flow
  initial_connected : IsConnected (Set.univ : Set M)

  local_topology :
    M72LocalTopologyService global.certificate.flow extinction.extinction_time
variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
  [SecondCountableTopology M]
variable {N : NormalizedInitialMetric (M := M)}

structure M72ReconstructionLedger (I : M72ReconstructionInput N) where
  event_times : Finset ℝ
  event_times_eq :
    (↑event_times : Set ℝ) =
      I.global.certificate.flow.surgery_times ∩
        Set.Icc 0 I.extinction.extinction_time

def M72EventIndex (I : M72ReconstructionInput N)
    (L : M72ReconstructionLedger I) :=
  L.event_times

theorem M72EventFlowMem (I : M72ReconstructionInput N)
    (L : M72ReconstructionLedger I) (e : M72EventIndex I L) :
    e.1 ∈ I.global.certificate.flow.surgery_times := by
  have h : e.1 ∈ (↑L.event_times : Set ℝ) := e.2
  rw [L.event_times_eq] at h
  exact h.1

theorem M72EventBeforeExtinction (I : M72ReconstructionInput N)
    (L : M72ReconstructionLedger I) (e : M72EventIndex I L) :
    e.1 ≤ I.extinction.extinction_time := by
  have h : e.1 ∈ (↑L.event_times : Set ℝ) := e.2
  rw [L.event_times_eq] at h
  exact h.2.2

def M72EventTopology (I : M72ReconstructionInput N)
    (L : M72ReconstructionLedger I) (e : M72EventIndex I L) :
    M72EventTopologyData I.global.certificate.flow e.1 (M72EventFlowMem I L e) :=
  I.local_topology.event e.1 (M72EventFlowMem I L e)
    (M72EventBeforeExtinction I L e)

def M72NonSurvivorIndex (I : M72ReconstructionInput N)
    (L : M72ReconstructionLedger I) (e : M72EventIndex I L) :=
  {i : Fin (M72EventTopology I L e).conclusion.piece_count //
    (M72EventTopology I L e).conclusion.kind i ≠ .survivor}

def M72SummandIndex (I : M72ReconstructionInput N)
    (L : M72ReconstructionLedger I) :=
  Σ e : M72EventIndex I L, M72NonSurvivorIndex I L e

structure M72ReconstructionConclusion
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    {N : NormalizedInitialMetric (M := M)}
    (I : M72ReconstructionInput N) where
  ledger : M72ReconstructionLedger I

  summand_count : ℕ
  summand_index : Fin summand_count → M72SummandIndex I ledger
  summand_index_bijective : Function.Bijective summand_index
  pieces : Fin summand_count → GeneralizedSliceCarrier
  piece_eq : ∀ j,
    pieces j =
      (M72EventTopology I ledger (summand_index j).1).conclusion.piece
        (summand_index j).2.1
  piece_kind : ∀ j,
    (M72EventTopology I ledger (summand_index j).1).conclusion.kind
        (summand_index j).2.1 ≠ .survivor

  survivor_transport :
    ∀ (e : M72EventIndex I ledger)
      (i : Fin (M72EventTopology I ledger e).conclusion.piece_count),
      (M72EventTopology I ledger e).conclusion.kind i = .survivor →
      M72SuccessorChoice I.global.certificate.flow I.extinction.extinction_time
        I.local_topology.event e.1
        (M72EventFlowMem I ledger e)
        (M72EventTopology I ledger e) i
  survivor_target_in_ledger :
    ∀ (e : M72EventIndex I ledger)
      (i : Fin (M72EventTopology I ledger e).conclusion.piece_count)
      (hsurvivor :
        (M72EventTopology I ledger e).conclusion.kind i = .survivor),
      ∃ e' : M72EventIndex I ledger,
        (survivor_transport e i hsurvivor).target_time = e'.1 ∧
        HEq (survivor_transport e i hsurvivor).target_event
          (M72EventTopology I ledger e')

  assembly : SmoothFiniteConnectedSumAssembly pieces
    (I.global.certificate.flow.slice 0)
  target_nonempty : Nonempty (I.global.certificate.flow.slice 0).carrier
  target_connected : IsConnected
    (Set.univ : Set (I.global.certificate.flow.slice 0).carrier)

end PoincareConjecture
