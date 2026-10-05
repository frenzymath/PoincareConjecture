import PoincareLib.Topology.Manifold.Surgery.Reconstruction.Transport
import Mathlib.Data.Finset.Max

/-!
# Corollary 15.4: immediate successor transports

This file selects the next surgery time in the finite ledger and records the
ordinary slab map from a surgery slice to the next event's reference slice.
The image of a survivor region is identified with the connected component of
the transported base point.  This is the chronology and component step used
in the reverse-time assembly of Morgan--Tian Corollary 15.4, pp. 358--359
(`references/derived/MT2007.txt:17861-17902`).
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT

/-- The successor's predecessor cannot lie strictly after the current event.

The proof uses the predecessor anchor and the minimality of the selected
successor.  Source: the successive-event choice in Corollary 15.4, printed
pp. 358--359.
-/
theorem m72SuccessorPredecessor_le
    {F : SurgeryFlowData.{u}} {T T' : ℝ}
    {hT' : T' ∈ F.surgery_times}
    (E' : M72EventTopologyData F T' hT')
    (hT : T ∈ F.surgery_times)
    (hminimal : ∀ s : ℝ, T < s → s ∈ F.surgery_times → T' ≤ s) :
    E'.predecessor ≤ T := by
  rcases E'.predecessor_anchor with hzero | hpred
  · rw [hzero]
    exact F.time_domain_nonnegative (F.surgery_times_subset hT)
  · by_contra hnot
    have hTp : T < E'.predecessor := lt_of_not_ge hnot
    have hpT' : E'.predecessor < T' :=
      E'.predecessor_lt.trans E'.pre_time_lt
    exact (not_lt_of_ge (hminimal E'.predecessor hTp hpred)) hpT'

/-- The selected successor event has the current event as predecessor.
Source: Corollary 15.4, printed pp. 358--359. -/
theorem m72SuccessorNextPredecessor
    {F : SurgeryFlowData.{u}} {T T' : ℝ}
    {hT' : T' ∈ F.surgery_times}
    (E' : M72EventTopologyData F T' hT')
    (hT : T ∈ F.surgery_times) (horder : T < T')
    (hminimal : ∀ s : ℝ, T < s → s ∈ F.surgery_times → T' ≤ s) :
    E'.predecessor = T := by
  have hle := m72SuccessorPredecessor_le E' hT hminimal
  apply le_antisymm hle
  by_contra hnot
  have hpt : E'.predecessor < T := lt_of_not_ge hnot
  by_cases hTpre : T ≤ E'.pre_time
  · exact Set.disjoint_left.mp E'.no_surgery_before hT ⟨hpt, hTpre⟩
  · exact Set.disjoint_left.mp E'.no_surgery_after hT
      ⟨lt_of_not_ge hTpre, horder⟩

/-- The next event's reference lies strictly after the current surgery.
Source: Corollary 15.4, printed pp. 358--359. -/
theorem m72SuccessorPreAfter
    {F : SurgeryFlowData.{u}} {T T' : ℝ}
    {hT' : T' ∈ F.surgery_times}
    (E' : M72EventTopologyData F T' hT')
    (hpredecessor : E'.predecessor = T) :
    T < E'.pre_time := by
  simpa [hpredecessor] using E'.predecessor_lt

/-- The ordinary slab interval to the successor lies in the flow domain.
Source: Corollary 15.4, printed pp. 358--359. -/
theorem m72SuccessorTimeDomain
    {F : SurgeryFlowData.{u}} {T T' : ℝ}
    {hT' : T' ∈ F.surgery_times}
    (E' : M72EventTopologyData F T' hT')
    (hpredecessor : E'.predecessor = T) :
    Set.Icc T E'.pre_time ⊆ F.time_domain := by
  simpa [hpredecessor] using E'.predecessor_time_domain

/-- There is no surgery in the ordinary slab before the successor reference.
Source: Corollary 15.4, printed pp. 358--359. -/
theorem m72SuccessorNoSurgery
    {F : SurgeryFlowData.{u}} {T T' : ℝ}
    {hT' : T' ∈ F.surgery_times}
    (E' : M72EventTopologyData F T' hT')
    (hpredecessor : E'.predecessor = T) :
    Disjoint F.surgery_times (Set.Ioc T E'.pre_time) := by
  simpa [hpredecessor] using E'.no_surgery_before

/-- A diffeomorphism carries a whole connected component to the component of
its image point.  Source: the ordinary transport in Corollary 15.4, printed
pp. 358--359. -/
theorem m72DiffeomorphImageConnectedComponent
    {A B : GeneralizedSliceCarrier.{u}}
    (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier B.carrier ∞)
    (x : A.carrier) :
    Set.image d (connectedComponent x) = connectedComponent (d x) := by
  simpa [connectedComponentIn_univ] using
    d.toHomeomorph.image_connectedComponentIn (s := (Set.univ : Set A.carrier))
      (x := x) (Set.mem_univ x)

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
  [SecondCountableTopology M]
  {N : NormalizedInitialMetric (M := M)}

/-- A survivor event strictly precedes the selected extinction time.
Source: the final empty slice in Corollary 15.4, printed pp. 358--359. -/
theorem m72SurvivorBeforeExtinction
    (I : M72ReconstructionInput N) (L : M72ReconstructionLedger I)
    (e : M72EventIndex I L)
    (i : Fin (M72EventTopology I L e).conclusion.piece_count)
    (hi : (M72EventTopology I L e).conclusion.kind i = .survivor) :
    e.1 < I.extinction.extinction_time := by
  have he_le : e.1 ≤ I.extinction.extinction_time :=
    M72EventBeforeExtinction I L e
  apply lt_of_le_of_ne he_le
  intro heq
  have hempty : IsEmpty
      (I.global.certificate.flow.slice e.1).carrier := by
    rw [heq]
    exact I.extinction.extinct
  have hnot :
      (M72EventTopology I L e).conclusion.kind i ≠ .survivor :=
    (M72EventTopology I L e).no_survivor_if_empty hempty i
  exact (hnot hi).elim

/-- Every event strictly before extinction has an immediate successor in the
ledger, minimal among all later surgery times.  No survivor is required.
Source: the finite-history induction in Corollary 15.4, printed pp. 358--359. -/
theorem m72ImmediateSuccessor
    (I : M72ReconstructionInput N) (L : M72ReconstructionLedger I)
    (e : M72EventIndex I L)
    (heH : e.1 < I.extinction.extinction_time) :
    ∃ e' : M72EventIndex I L, e.1 < e'.1 ∧
      ∀ s : ℝ, e.1 < s → s ∈ I.global.certificate.flow.surgery_times →
        e'.1 ≤ s := by
  classical
  let F := I.global.certificate.flow
  let H := I.extinction.extinction_time
  have hHnonnegative : 0 ≤ H :=
    F.time_domain_nonnegative I.extinction.extinction_mem
  have hHledger : H ∈ (↑L.event_times : Set ℝ) := by
    rw [L.event_times_eq]
    exact ⟨I.extinction.extinction_surgery_mem, hHnonnegative, le_rfl⟩
  let later : Finset ℝ := L.event_times.filter (fun s => e.1 < s)
  have hlater : later.Nonempty := by
    refine ⟨H, Finset.mem_filter.mpr ⟨hHledger, heH⟩⟩
  let T' : ℝ := later.min' hlater
  have hT'later : T' ∈ later := Finset.min'_mem later hlater
  have hT'ledger : T' ∈ (↑L.event_times : Set ℝ) :=
    (Finset.mem_filter.mp hT'later).1
  have hT'leH : T' ≤ H := by
    have h := hT'ledger
    rw [L.event_times_eq] at h
    exact h.2.2
  have hminimal : ∀ s : ℝ, e.1 < s → s ∈ F.surgery_times → T' ≤ s := by
    intro s hes hs
    by_cases hsH : s ≤ H
    · have hsnonnegative : 0 ≤ s :=
        F.time_domain_nonnegative (F.surgery_times_subset hs)
      have hsledger : s ∈ (↑L.event_times : Set ℝ) := by
        rw [L.event_times_eq]
        exact ⟨hs, hsnonnegative, hsH⟩
      exact Finset.min'_le later s
        (Finset.mem_filter.mpr ⟨hsledger, hes⟩)
    · exact hT'leH.trans (le_of_lt (lt_of_not_ge hsH))
  exact ⟨⟨T', hT'ledger⟩, (Finset.mem_filter.mp hT'later).2, hminimal⟩

/-- The first ledger event is anchored at the initial time.
Source: the final ordinary interval in Corollary 15.4, printed pp. 358--359. -/
theorem m72FirstEventPredecessor
    (I : M72ReconstructionInput N) (L : M72ReconstructionLedger I)
    (e : M72EventIndex I L)
    (hfirst : ∀ e' : M72EventIndex I L, e.1 ≤ e'.1) :
    (M72EventTopology I L e).predecessor = 0 := by
  let E := M72EventTopology I L e
  rcases E.predecessor_anchor with hzero | hmem
  · exact hzero
  have hnonnegative : 0 ≤ E.predecessor :=
    I.global.certificate.flow.time_domain_nonnegative
      (I.global.certificate.flow.surgery_times_subset hmem)
  have hlt : E.predecessor < e.1 := E.predecessor_lt.trans E.pre_time_lt
  have hledger : E.predecessor ∈ (↑L.event_times : Set ℝ) := by
    rw [L.event_times_eq]
    exact ⟨hmem, hnonnegative, hlt.le.trans (M72EventBeforeExtinction I L e)⟩
  exact (not_lt_of_ge (hfirst ⟨E.predecessor, hledger⟩) hlt).elim

/-- Construct the complete immediate-successor record for a survivor piece.

The target is the minimum ledger time strictly after the source event.  Its
predecessor, reference interval, regular transport, and component image are
then supplied by the event data and the preceding chronology lemmas.
Source: Corollary 15.4, printed pp. 358--359.
-/
noncomputable def m72SuccessorChoice
    (I : M72ReconstructionInput N) (L : M72ReconstructionLedger I)
    (e : M72EventIndex I L)
    (i : Fin (M72EventTopology I L e).conclusion.piece_count)
    (hi : (M72EventTopology I L e).conclusion.kind i = .survivor) :
    M72SuccessorChoice I.global.certificate.flow I.extinction.extinction_time
      I.local_topology.event e.1 (M72EventFlowMem I L e)
      (M72EventTopology I L e) i := by
  let F := I.global.certificate.flow
  let hexists := m72ImmediateSuccessor I L e
    (m72SurvivorBeforeExtinction I L e i hi)
  let e' := Classical.choose hexists
  have horder : e.1 < e'.1 := (Classical.choose_spec hexists).1
  have hminimal : ∀ s : ℝ, e.1 < s → s ∈ F.surgery_times → e'.1 ≤ s :=
    (Classical.choose_spec hexists).2
  let E' := M72EventTopology I L e'
  have hnext : E'.predecessor = e.1 :=
    m72SuccessorNextPredecessor E' (M72EventFlowMem I L e)
      horder hminimal
  have hpre : e.1 < E'.pre_time := m72SuccessorPreAfter E' hnext
  have hdomain : Set.Icc e.1 E'.pre_time ⊆ F.time_domain :=
    m72SuccessorTimeDomain E' hnext
  have hnosurgery : Disjoint F.surgery_times (Set.Ioc e.1 E'.pre_time) :=
    m72SuccessorNoSurgery E' hnext
  let d : Diffeomorph (𝓡 3) (𝓡 3)
      (F.slice e.1).carrier (F.slice E'.pre_time).carrier ∞ :=
    (F.regular_slabs e.1 E'.pre_time hpre hdomain hnosurgery).identify
      ⟨E'.pre_time, ⟨hpre.le, le_rfl⟩⟩
  let hcomponent := (M72EventTopology I L e).conclusion.survivor_component i hi
  let x := Classical.choose hcomponent
  have hx := Classical.choose_spec hcomponent
  refine
    { target_time := e'.1
      target_mem := M72EventFlowMem I L e'
      target_before := M72EventBeforeExtinction I L e'
      successor :=
        { order := horder
          target_horizon := M72EventBeforeExtinction I L e'
          next_minimal := hminimal
          next_predecessor := hnext
          pre_after := hpre
          time_domain := hdomain
          no_surgery := hnosurgery
          transport := d
          transport_eq_regular := fun y => rfl
          component_point := d x
          survivor_image := ?_ } }
  rw [hx]
  exact m72DiffeomorphImageConnectedComponent d x

end PoincareMT
