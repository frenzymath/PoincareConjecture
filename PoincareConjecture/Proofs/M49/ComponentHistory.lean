import PoincareConjecture.Proofs.M49.EventComponents
import PoincareConjecture.Proofs.M49.InitialComponents
import PoincareConjecture.Proofs.M49.FlowEventCounts
import PoincareConjecture.Proofs.M49.Lemma17_12_EventHistory
import PoincareConjecture.Proofs.M49.Mathlib.ComponentCardinality
import PoincareConjecture.Proofs.M49.Mathlib.FiniteJumpBalance
import Mathlib.Topology.Instances.Nat










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

universe u

namespace PoincareConjecture.M49



theorem regular_component_count_eq (F : SurgeryFlowData.{u})
    {a b : ℝ} (hab : a ≤ b) (hJ : Icc a b ⊆ F.time_domain)
    (hno : Disjoint F.surgery_times (Ioc a b)) :
    Nat.card (ConnectedComponents (F.slice b).carrier) =
      Nat.card (ConnectedComponents (F.slice a).carrier) := by
  rcases lt_or_eq_of_le hab with hab | rfl
  · let S := F.regular_slabs a b hab hJ hno
    exact (S.identify ⟨b, hab.le, le_rfl⟩).toHomeomorph.card_connectedComponents_eq.symm
  · rfl



theorem event_component_count_tendsto
    {g0 : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
    {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
    (E : SurgeryEventData g0 K P slice metric T) :
    Tendsto (fun t => Nat.card (ConnectedComponents (slice t).carrier))
      (𝓝[<] T) (𝓝 (Nat.card (ConnectedComponents (slice E.tMinus).carrier))) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsLT E.tMinus_lt] with t ht
  exact (E.pre_identify ⟨t, ht.1.le, ht.2⟩).toHomeomorph.card_connectedComponents_eq



theorem vanishing_component_count_tendsto
    {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
    (E : SurgeryVanishingEventData P slice metric T) :
    Tendsto (fun t => Nat.card (ConnectedComponents (slice t).carrier))
      (𝓝[<] T) (𝓝 (Nat.card (ConnectedComponents (slice E.tMinus).carrier))) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [Ioo_mem_nhdsLT E.tMinus_lt] with t ht
  exact (E.pre_identify ⟨t, ht.1.le, ht.2⟩).toHomeomorph.card_connectedComponents_eq




theorem event_component_jump_balance (F : SurgeryFlowData.{u})
    (T : ℝ) (hT : T ∈ F.surgery_times)
    (hdiscard : ∀ [Nonempty (F.slice T).carrier],
      (F.event T hT).cap_count = 0 →
        ∃ x : (F.slice (F.event T hT).tMinus).carrier,
          connectedComponent x ⊆ (F.event T hT).retained_preᶜ) :
    ∃ L : ℕ,
      Tendsto (fun t => Nat.card (ConnectedComponents (F.slice t).carrier))
        (𝓝[<] T) (𝓝 L) ∧
      Nat.card (ConnectedComponents (F.slice T).carrier) + eventDeletionCount F T ≤
        L + eventCapCount F T := by
  classical
  rcases isEmpty_or_nonempty (F.slice T).carrier with hEmpty | hNonempty
  · let := hEmpty
    let E := F.vanishing_event T hT
    have hpre : E.tMinus ∈ F.time_domain :=
      vanishingEventPreInterval F T hT ⟨le_rfl, E.tMinus_lt⟩
    let := slice_components_finite F hpre
    let := E.pre_nonempty
    have hpos : 1 ≤ Nat.card (ConnectedComponents (F.slice E.tMinus).carrier) :=
      Nat.succ_le_of_lt Nat.card_pos
    have hpost : Nat.card (ConnectedComponents (F.slice T).carrier) = 0 := by
      apply Nat.card_eq_zero.mpr
      refine Or.inl ⟨fun c => ?_⟩
      obtain ⟨y, _⟩ := ConnectedComponents.surjective_coe c
      exact isEmptyElim y
    refine ⟨_, vanishing_component_count_tendsto E, ?_⟩
    simpa [eventDeletionCount_eq F T hT, eventCapCount_eq_zero_of_isEmpty F T, hpost]
      using hpos
  · let := hNonempty
    let E := F.event T hT
    have hpre : E.tMinus ∈ F.time_domain :=
      nonemptyEventPreInterval F T hT ⟨le_rfl, E.tMinus_lt⟩
    let := slice_components_finite F hpre
    have hcap : eventCapCount F T = E.cap_count := eventCapCount_eq F T hT
    refine ⟨_, event_component_count_tendsto E, ?_⟩
    by_cases hzero : E.cap_count = 0
    · obtain ⟨x, hx⟩ := hdiscard hzero
      simpa [eventDeletionCount_eq F T hT, hcap, hzero] using
        event_components_card_add_one_le E hzero x hx
    · simpa [eventDeletionCount_eq F T hT, hcap, hzero] using event_components_card_le E



theorem component_history_balance (F : SurgeryFlowData.{u}) {b : ℝ}
    (hb : b ∈ F.time_domain)
    (hdiscard : ∀ (T : ℝ) (hT : T ∈ F.surgery_times), T ∈ Icc 0 b →
      ∀ [Nonempty (F.slice T).carrier], (F.event T hT).cap_count = 0 →
        ∃ x : (F.slice (F.event T hT).tMinus).carrier,
          connectedComponent x ⊆ (F.event T hT).retained_preᶜ)
    (S : Finset ℝ) (hS : (S : Set ℝ) = F.surgery_times ∩ Ioc 0 b) :
    Nat.card (ConnectedComponents (F.slice b).carrier) +
        ∑ T ∈ S, eventDeletionCount F T ≤
      Nat.card (ConnectedComponents (F.slice 0).carrier) +
        ∑ T ∈ S, eventCapCount F T := by
  have hmem (t : ℝ) : t ∈ S ↔ t ∈ F.surgery_times ∩ Ioc 0 b := by
    change t ∈ (S : Set ℝ) ↔ _
    rw [hS]
  apply add_sum_le_add_sum_of_finite_left_jumps S (F.time_domain_nonnegative hb)
    (fun t ht => ((hmem t).mp ht).2)
  · intro x hx y hy hxy hdisjoint
    have hno : Disjoint F.surgery_times (Ioc x y) := by
      apply disjoint_left.mpr
      intro z hz hzxy
      exact disjoint_left.mp hdisjoint
        ((hmem z).mpr ⟨hz, hx.1.trans_lt hzxy.1, hzxy.2.trans hy.2⟩) hzxy
    have hJ : Icc x y ⊆ F.time_domain := fun t ht => initialInterval_subset F hb
      ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩
    exact (regular_component_count_eq F hxy hJ hno).le
  · intro T hTS
    have hT := (hmem T).mp hTS
    exact event_component_jump_balance F T hT.1
      (hdiscard T hT.1 ⟨hT.2.1.le, hT.2.2⟩)




theorem event_card_le_initial_add_twice_caps (F : SurgeryFlowData.{u}) {b : ℝ}
    (hb : b ∈ F.time_domain)
    (hdiscard : ∀ (T : ℝ) (hT : T ∈ F.surgery_times), T ∈ Icc 0 b →
      ∀ [Nonempty (F.slice T).carrier], (F.event T hT).cap_count = 0 →
        ∃ x : (F.slice (F.event T hT).tMinus).carrier,
          connectedComponent x ⊆ (F.event T hT).retained_preᶜ)
    (S : Finset ℝ) (hS : (S : Set ℝ) = F.surgery_times ∩ Ioc 0 b) :
    S.card ≤ Nat.card (ConnectedComponents (F.slice 0).carrier) +
      2 * ∑ T ∈ S, eventCapCount F T := by
  have hcount : S.card ≤ (∑ T ∈ S, eventCapCount F T) +
      ∑ T ∈ S, eventDeletionCount F T := by
    calc
      S.card = ∑ _T ∈ S, (1 : ℕ) := by simp
      _ ≤ ∑ T ∈ S, (eventCapCount F T + eventDeletionCount F T) := by
        apply Finset.sum_le_sum
        intro T hT
        apply one_le_event_counts F T
        have hTS : T ∈ (S : Set ℝ) := hT
        rw [hS] at hTS
        exact hTS.1
      _ = _ := Finset.sum_add_distrib
  have hbalance := component_history_balance F hb hdiscard S hS
  omega

end PoincareConjecture.M49
