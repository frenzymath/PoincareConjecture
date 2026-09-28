import PoincareConjecture.Definitions.M72FiniteReconstruction
import Mathlib.Data.Finset.Max

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

private structure M72Predecessor (F : SurgeryFlowData.{u}) (T : ℝ) where
  time : ℝ
  nonnegative : 0 ≤ time
  before : time < T
  anchor : time = 0 ∨ time ∈ F.surgery_times
  no_surgery : Disjoint F.surgery_times (Set.Ioo time T)

private structure M72Reference (F : SurgeryFlowData.{u}) (T r : ℝ) where
  time : ℝ
  nonnegative : 0 ≤ time
  before : time < T
  after_reference : r < time
  predecessor : ℝ
  predecessor_anchor : predecessor = 0 ∨ predecessor ∈ F.surgery_times
  predecessor_lt : predecessor < time
  no_surgery_before : Disjoint F.surgery_times (Set.Ioc predecessor time)
  no_surgery_after : Disjoint F.surgery_times (Set.Ioo time T)
  time_domain : Set.Icc predecessor time ⊆ F.time_domain
  transport : Diffeomorph (𝓡 3) (𝓡 3)
    (F.slice predecessor).carrier (F.slice time).carrier ∞
  transport_eq : ∀ x, transport x =
    (F.regular_slabs predecessor time predecessor_lt time_domain
      no_surgery_before).identify ⟨time, ⟨predecessor_lt.le, le_rfl⟩⟩ x

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
  [SecondCountableTopology M]
  {N : NormalizedInitialMetric (M := M)}

private noncomputable def m72Predecessor
    (G : GlobalSurgeryFlowCertificate N)
    (T : ℝ) (hT : T ∈ G.flow.surgery_times) :
    M72Predecessor G.flow T := by
  classical
  have hTnonnegative : 0 ≤ T :=
    G.flow.time_domain_nonnegative (G.flow.surgery_times_subset hT)
  have hTne : T ≠ 0 := by
    intro h
    exact G.flow.zero_not_surgery (h ▸ hT)
  have hTpositive : 0 < T := lt_of_le_of_ne hTnonnegative hTne.symm
  let bounded := (G.local_finite (Set.Icc 0 T) isCompact_Icc).toFinset
  have mem_bounded : ∀ s : ℝ, s ∈ bounded ↔
      s ∈ G.flow.surgery_times ∧ 0 ≤ s ∧ s ≤ T := by
    intro s
    simp only [bounded, Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_Icc]
  let earlier := insert 0 (bounded.filter (fun s => s < T))
  have hzero : 0 ∈ earlier := Finset.mem_insert_self _ _
  let p := earlier.max' ⟨0, hzero⟩
  have hp_mem : p ∈ earlier := earlier.max'_mem _
  have hp_nonnegative : 0 ≤ p := earlier.le_max' 0 hzero
  have hp_lt : p < T := by
    rcases Finset.mem_insert.mp hp_mem with hp | hp
    · simpa only [hp] using hTpositive
    · exact (Finset.mem_filter.mp hp).2
  have hp_anchor : p = 0 ∨ p ∈ G.flow.surgery_times := by
    rcases Finset.mem_insert.mp hp_mem with hp | hp
    · exact Or.inl hp
    · exact Or.inr ((mem_bounded p).mp (Finset.mem_filter.mp hp).1).1
  refine
    { time := p
      nonnegative := hp_nonnegative
      before := hp_lt
      anchor := hp_anchor
      no_surgery := ?_ }
  apply Set.disjoint_left.mpr
  intro s hs hps
  have hs_nonnegative :=
    G.flow.time_domain_nonnegative (G.flow.surgery_times_subset hs)
  have hs_mem : s ∈ earlier := Finset.mem_insert_of_mem
    (Finset.mem_filter.mpr ⟨(mem_bounded s).mpr
      ⟨hs, hs_nonnegative, hps.2.le⟩, hps.2⟩)
  exact (not_lt_of_ge (earlier.le_max' s hs_mem)) hps.1

private noncomputable def m72Reference
    (G : GlobalSurgeryFlowCertificate N)
    (T : ℝ) (hT : T ∈ G.flow.surgery_times)
    (r : ℝ) (hr : r < T) : M72Reference G.flow T r := by
  let P := m72Predecessor G T hT
  let q := (max P.time r + T) / 2
  have hmax : max P.time r < T := max_lt P.before hr
  have hmaxq : max P.time r < q := by dsimp [q]; linarith
  have hqT : q < T := by dsimp [q]; linarith
  have hpq : P.time < q := (le_max_left P.time r).trans_lt hmaxq
  have hrq : r < q := (le_max_right P.time r).trans_lt hmaxq
  have hbefore : Disjoint G.flow.surgery_times (Set.Ioc P.time q) := by
    apply Set.disjoint_left.mpr
    intro s hs hsI
    exact Set.disjoint_left.mp P.no_surgery hs
      ⟨hsI.1, hsI.2.trans_lt hqT⟩
  have hafter : Disjoint G.flow.surgery_times (Set.Ioo q T) := by
    apply Set.disjoint_left.mpr
    intro s hs hsI
    exact Set.disjoint_left.mp P.no_surgery hs ⟨hpq.trans hsI.1, hsI.2⟩
  have hdomain : Set.Icc P.time q ⊆ G.flow.time_domain := by
    intro s hs
    rw [G.time_domain_eq]
    exact P.nonnegative.trans hs.1
  exact
    { time := q
      nonnegative := P.nonnegative.trans hpq.le
      before := hqT
      after_reference := hrq
      predecessor := P.time
      predecessor_anchor := P.anchor
      predecessor_lt := hpq
      no_surgery_before := hbefore
      no_surgery_after := hafter
      time_domain := hdomain
      transport := (G.flow.regular_slabs P.time q hpq hdomain hbefore).identify
        ⟨q, ⟨hpq.le, le_rfl⟩⟩
      transport_eq := fun _ => rfl }

private noncomputable def m72NonemptyEventFromRaw
    (G : GlobalSurgeryFlowCertificate N)
    (L : RawLocalSurgeryTopologyData G.flow)
    (T : ℝ) (hT : T ∈ G.flow.surgery_times)
    [hN : Nonempty (G.flow.slice T).carrier] :
    M72EventTopologyData G.flow T hT := by
  let E := G.flow.event T hT
  let R := m72Reference G T hT E.tMinus E.tMinus_lt
  let C := Classical.choice (L.nonempty_reconstruction T hT)
  exact
    { pre_time := R.time
      pre_time_nonnegative := R.nonnegative
      pre_time_lt := R.before
      conclusion := C.conclusion.transportPre
        (E.pre_identify ⟨R.time, ⟨R.after_reference.le, R.before⟩⟩)
      nonempty_reference := fun _ => R.after_reference
      vanishing_reference := fun hE => (hE.false (Classical.choice hN)).elim
      cap_correspondence := fun _ i => C.cap_correspondence.cap_piece i
      no_survivor_if_empty := fun hE => (hE.false (Classical.choice hN)).elim
      predecessor := R.predecessor
      predecessor_anchor := R.predecessor_anchor
      predecessor_lt := R.predecessor_lt
      no_surgery_before := R.no_surgery_before
      no_surgery_after := R.no_surgery_after
      predecessor_time_domain := R.time_domain
      predecessor_transport := R.transport
      predecessor_transport_eq_regular := R.transport_eq }

private noncomputable def m72VanishingEventFromRaw
    (G : GlobalSurgeryFlowCertificate N)
    (L : RawLocalSurgeryTopologyData G.flow)
    (T : ℝ) (hT : T ∈ G.flow.surgery_times)
    [hE : IsEmpty (G.flow.slice T).carrier] :
    M72EventTopologyData G.flow T hT := by
  let E := G.flow.vanishing_event T hT
  let R := m72Reference G T hT E.tMinus E.tMinus_lt
  let C := Classical.choice (L.vanishing_reconstruction T hT)
  exact
    { pre_time := R.time
      pre_time_nonnegative := R.nonnegative
      pre_time_lt := R.before
      conclusion := C.conclusion.transportPre
        (E.pre_identify ⟨R.time, ⟨R.after_reference.le, R.before⟩⟩)
      nonempty_reference := fun hN => (hE.false (Classical.choice hN)).elim
      vanishing_reference := fun _ => R.after_reference
      cap_correspondence := fun hN => (hE.false (Classical.choice hN)).elim
      no_survivor_if_empty := fun _ => C.no_survivor
      predecessor := R.predecessor
      predecessor_anchor := R.predecessor_anchor
      predecessor_lt := R.predecessor_lt
      no_surgery_before := R.no_surgery_before
      no_surgery_after := R.no_surgery_after
      predecessor_time_domain := R.time_domain
      predecessor_transport := R.transport
      predecessor_transport_eq_regular := R.transport_eq }

private noncomputable def m72EventFromRaw
    (G : GlobalSurgeryFlowCertificate N)
    (L : RawLocalSurgeryTopologyData G.flow)
    (T : ℝ) (hT : T ∈ G.flow.surgery_times) :
    M72EventTopologyData G.flow T hT := by
  classical
  exact if hN : Nonempty (G.flow.slice T).carrier then
    by
      letI := hN
      exact m72NonemptyEventFromRaw G L T hT
  else
    by
      letI := not_nonempty_iff.mp hN
      exact m72VanishingEventFromRaw G L T hT

noncomputable def m72LocalTopologyFromRaw
    (G : GlobalSurgeryFlowCertificate N)
    (L : RawLocalSurgeryTopologyData G.flow) (H : ℝ) :
    M72LocalTopologyService G.flow H where
  admissible := L.admissible
  m38_data := L
  event := fun T hT _ => m72EventFromRaw G L T hT
  m38_nonempty_source := by
    intro T hT _ hN
    have hbranch : m72EventFromRaw G L T hT =
        m72NonemptyEventFromRaw G L T hT := by
      unfold m72EventFromRaw
      exact dif_pos hN
    rw [hbranch]
    rfl
  m38_vanishing_source := by
    intro T hT _ hE
    have hN : ¬ Nonempty (G.flow.slice T).carrier :=
      fun h => hE.false (Classical.choice h)
    have hbranch : m72EventFromRaw G L T hT =
        m72VanishingEventFromRaw G L T hT := by
      unfold m72EventFromRaw
      exact dif_neg hN
    rw [hbranch]
    rfl

end PoincareConjecture
