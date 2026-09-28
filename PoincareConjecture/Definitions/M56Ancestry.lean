import PoincareConjecture.Definitions.Ch15.SurgeryComparison
import PoincareConjecture.Definitions.M52GlobalFlow
import PoincareConjecture.Definitions.M38LocalTopology
import PoincareConjecture.Definitions.M55ChildComponents

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedEventChildWitness (F : SurgeryFlowData.{u}) where
  topology : ∀ (T : ℝ) (hT : T ∈ F.surgery_times)
      (hpost : Nonempty (F.slice T).carrier),
    letI := hpost
    SurgeryTopologyConclusion
      (F.slice (F.event T hT).tMinus) (F.slice T)
  effects : ∀ (T : ℝ) (hT : T ∈ F.surgery_times)
      (hpost : Nonempty (F.slice T).carrier),
    letI := hpost
    RepairedSurgeryGroupEffectsData (topology T hT hpost)
  children : ∀ (T : ℝ) (hT : T ∈ F.surgery_times)
      (hpost : Nonempty (F.slice T).carrier),
    letI := hpost
    RepairedChildComponentsData (topology T hT hpost) (effects T hT hpost)
  parent_groups_subsingleton : ∀ (T : ℝ) (hT : T ∈ F.surgery_times)
      (hpost : Nonempty (F.slice T).carrier),
    letI := hpost
    ∀ i : Fin (topology T hT hpost).piece_count,
      ∀ hi : (topology T hT hpost).kind i = .survivor,
        ∀ x : ((topology T hT hpost).piece i).carrier,
          Subsingleton (FundamentalGroup
            (F.slice (F.event T hT).tMinus).carrier
            ((effects T hT hpost).parent_basepoint i hi x))

structure RepairedComponentPath
    (F : SurgeryFlowData.{u}) (T : ℝ)
    (W : RepairedEventChildWitness F) where

  terminal_mem : T ∈ F.time_domain
  component : ∀ s : Set.Icc (0 : ℝ) T,
    SurgerySelectedComponent (F.slice s.1)
  time_subset : Set.Icc (0 : ℝ) T ⊆ F.time_domain
  surgery_times : Finset ℝ
  surgery_times_eq : (↑surgery_times : Set ℝ) =
    F.surgery_times ∩ Set.Icc 0 T
  regular_transport : ∀ (a b : Set.Icc (0 : ℝ) T) (_hab : a.1 < b.1)
      (_hdisjoint : Disjoint F.surgery_times (Set.Ioc a.1 b.1)),
      Diffeomorph (𝓡 3) (𝓡 3)
        (component a).carrier.carrier (component b).carrier.carrier ∞
  regular_transport_ambient : ∀ (a b : Set.Icc (0 : ℝ) T)
      (hab : a.1 < b.1)
      (hdisjoint : Disjoint F.surgery_times (Set.Ioc a.1 b.1)),
      ∀ x,
        (component b).inclusion
            ((regular_transport a b hab hdisjoint) x) =
          (F.regular_slabs a.1 b.1 hab
            (fun _u hu => time_subset ⟨a.2.1.trans hu.1, hu.2.trans b.2.2⟩)
            hdisjoint).transport
            ⟨a.1, ⟨le_rfl, hab.le⟩⟩
            ⟨b.1, ⟨hab.le, le_rfl⟩⟩
            ((component a).inclusion x)
  event_survivor_index : ∀ (s : Set.Icc (0 : ℝ) T)
      (hs : s.1 ∈ F.surgery_times)
      (hpost : Nonempty (F.slice s.1).carrier),
      letI := hpost
      Fin (W.topology s.1 hs hpost).piece_count
  event_survivor_index_kind : ∀ (s : Set.Icc (0 : ℝ) T)
      (hs : s.1 ∈ F.surgery_times)
      (hpost : Nonempty (F.slice s.1).carrier),
      letI := hpost
      (W.topology s.1 hs hpost).kind
          (event_survivor_index s hs hpost) = .survivor
  event_survivor : ∀ (s : Set.Icc (0 : ℝ) T)
      (hs : s.1 ∈ F.surgery_times)
      (hpost : Nonempty (F.slice s.1).carrier),
      letI := hpost
      (Set.range (component s).inclusion =
        (W.topology s.1 hs hpost).survivor_region
          (event_survivor_index s hs hpost)) ∧
      (W.topology s.1 hs hpost).survivor_region
          (event_survivor_index s hs hpost) =
        connectedComponent
          ((W.children s.1 hs hpost).survivor_component_point
            (event_survivor_index s hs hpost)
            (event_survivor_index_kind s hs hpost))
  event_time_mem : ∀ (s : Set.Icc (0 : ℝ) T)
      (hs : s.1 ∈ F.surgery_times)
      (hpost : Nonempty (F.slice s.1).carrier),
      letI := hpost
      (F.event s.1 hs).tMinus ∈ F.time_domain
  survivor_piece_equivalence : ∀ (s : Set.Icc (0 : ℝ) T)
      (hs : s.1 ∈ F.surgery_times)
      (hpost : Nonempty (F.slice s.1).carrier),
      letI := hpost
      ∃ e : Diffeomorph (𝓡 3) (𝓡 3)
          ((W.topology s.1 hs hpost).piece
            (event_survivor_index s hs hpost)).carrier
          (component s).carrier.carrier ∞,
        (∀ y,
          (component s).inclusion (e y) =
            ((W.topology s.1 hs hpost).survivor
              (event_survivor_index s hs hpost)
              (event_survivor_index_kind s hs hpost)).map y)
  surgery_transition_inherited : ∀ (s : Set.Icc (0 : ℝ) T)
      (hs : s.1 ∈ F.surgery_times)
      (hpost : Nonempty (F.slice s.1).carrier),
      letI := hpost
      ∃ x : (component ⟨(F.event s.1 hs).tMinus,
          ⟨(F.event s.1 hs).tMinus_nonnegative,
            (F.event s.1 hs).tMinus_lt.le.trans s.2.2⟩⟩).carrier.carrier,
        (component ⟨(F.event s.1 hs).tMinus,
          ⟨(F.event s.1 hs).tMinus_nonnegative,
            (F.event s.1 hs).tMinus_lt.le.trans s.2.2⟩⟩).inclusion x ∈
            interior (F.event s.1 hs).retained_pre ∧
        (F.event s.1 hs).retention.map
            ((component ⟨(F.event s.1 hs).tMinus,
              ⟨(F.event s.1 hs).tMinus_nonnegative,
                (F.event s.1 hs).tMinus_lt.le.trans s.2.2⟩⟩).inclusion x) ∈
          Set.range (component s).inclusion
  group_persistence_input :
    RepairedGroupPersistenceInput F T component
  group_persistence :
    Nonempty (RepairedGroupPersistenceData F T component group_persistence_input)
structure RepairedFiniteAncestryData (F : SurgeryFlowData.{u})
    (W : RepairedEventChildWitness F) where

  initial_component : SurgerySelectedComponent (F.slice 0)
  initial_component_cover : Set.range initial_component.inclusion = Set.univ
  path_for : ∀ (T : ℝ) (_hT : T ∈ F.time_domain)
      (_x : (F.slice T).carrier),
      RepairedComponentPath F T W
  path_for_initial : ∀ (T : ℝ) (hT : T ∈ F.time_domain)
      (x : (F.slice T).carrier),
      (path_for T hT x).component
          ⟨0, le_rfl, F.time_domain_nonnegative hT⟩ = initial_component
  path_for_terminal_cover : ∀ (T : ℝ) (hT : T ∈ F.time_domain)
      (x : (F.slice T).carrier),
      x ∈ Set.range
        ((path_for T hT x).component
          ⟨T, ⟨F.time_domain_nonnegative hT, le_rfl⟩⟩).inclusion
  finite_path_cover : ∀ (T : ℝ) (hT : T ∈ F.time_domain),
    ∃ n : ℕ, ∃ paths : Fin n → RepairedComponentPath F T W,
      ∀ x : (F.slice T).carrier,
        ∃ i : Fin n,
          x ∈ Set.range
            ((paths i).component
              ⟨T, ⟨F.time_domain_nonnegative hT, le_rfl⟩⟩).inclusion
  bounded_event_count : ∀ H : ℝ, 0 ≤ H →
    (F.surgery_times ∩ Set.Icc 0 H).Finite

structure M56PoincareAncestryData (F : SurgeryFlowData.{u})
    (L : RawLocalSurgeryTopologyData F) where
  witness : RepairedEventChildWitness F
  topology_source : ∀ (T : ℝ) (hT : T ∈ F.surgery_times)
      (hpost : Nonempty (F.slice T).carrier),
    letI := hpost
    witness.topology T hT hpost =
      (Classical.choice (L.nonempty_reconstruction T hT)).conclusion
  ancestry : RepairedFiniteAncestryData F witness
  component_simply_connected : ∀ (t : ℝ), t ∈ F.time_domain →
    ∀ C : SurgerySelectedComponent (F.slice t),
      SimplyConnectedSpace C.carrier.carrier

end PoincareConjecture
