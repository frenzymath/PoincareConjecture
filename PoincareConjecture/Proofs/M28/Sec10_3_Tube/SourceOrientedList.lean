import PoincareConjecture.Proofs.M28.Mathlib.ConsistentListLift
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceOrientationCompatibility
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceMinimizerEdgePacket
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceFrontierSelection










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

open PoincareConjecture.EpsilonNeck



structure SourceOrientedList {epsilon C A D₀ D : ℝ}
    {E : SameTimeCounterexample.{u} epsilon C A D₀ D}
    (S : CounterexampleNeckSegment E) where
  nodes : List (ℝ × EpsilonNeck (E.flow.metric E.time))
  nonempty : nodes ≠ []
  head_time : (nodes.head nonempty).1 = S.lower
  terminal : MapsTo S.path (Icc (nodes.getLast nonempty).1 S.upper)
    (nodes.getLast nonempty).2.carrier
  vertex : ∀ p ∈ nodes, p.1 ∈ Icc S.lower S.upper ∧
    ∃ N ∈ S.cover.necks, (p.2 = N ∨ p.2 = N.reversed) ∧ S.path p.1 = p.2.center
  edges : nodes.IsChain (fun p q => p.1 < q.1 ∧
    ∃ P ∈ S.cover.necks,
      SourceEdgeCommonOrientationPacket p.2 P q.2 (γ := S.path) p.1 q.1 ∧
      SourceEdgePacket p.2 q.2 epsilon)
  covers : MapsTo S.path (Icc S.lower S.upper)
    {x | ∃ p ∈ nodes, x ∈ p.2.carrier}



theorem exists_source_oriented_list_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 10000 : ℝ) ∧
      ∀ {epsilon C A D₀ D : ℝ} (E : SameTimeCounterexample.{u} epsilon C A D₀ D)
        (S : CounterexampleNeckSegment E),
        0 < E.flow.scalar ⟨E.time, E.basepoint⟩ → epsilon ≤ epsilon₀ →
          Nonempty (SourceOrientedList S) := by
  obtain ⟨epsilonE, hEpos, hEsmall, hE⟩ :=
    exists_source_minimizer_edge_packet_accuracy.{u}
  obtain ⟨epsilonR, hRpos, _, hR⟩ := exists_source_neck_region_accuracy.{u}
  refine ⟨min epsilonE epsilonR, lt_min hEpos hRpos,
    (min_le_left _ _).trans hEsmall, ?_⟩
  intro epsilon C A D₀ D E S hbase hsmall
  obtain ⟨n, hn, tail, htimes, hchain, hlast, hcover⟩ := S.exists_frontier_neck_selection
  let times := S.lower :: tail
  let choice (s : ℝ) (N : EpsilonNeck (E.flow.metric E.time)) :=
    N = n s ∨ N = (n s).reversed
  let R (s t : ℝ) := s < t ∧ S.path t ∈ frontier (n s).carrier ∧
    MapsTo S.path (Ico s t) (n s).carrier
  let edge (s : ℝ) (N : EpsilonNeck (E.flow.metric E.time))
      (t : ℝ) (Q : EpsilonNeck (E.flow.metric E.time)) :=
    choice s N ∧ s < t ∧
      SourceEdgeCommonOrientationPacket N (n t) Q (γ := S.path) s t ∧
      SourceEdgePacket N Q epsilon
  have hvertex (s : ℝ) (_hs : s ∈ times) : ∃ N, choice s N :=
    ⟨n s, Or.inl rfl⟩
  have hedge (s : ℝ) (hs : s ∈ times) (t : ℝ) (ht : t ∈ times) (hst : R s t) :
      ∃ N Q, choice s N ∧ choice t Q ∧ edge s N t Q := by
    have hs' := htimes s hs
    have ht' := htimes t ht
    obtain ⟨N, Q, hN, H, hpacket⟩ := hE E S hbase
      (hsmall.trans (min_le_left _ _)) (n s) (hn s hs').1 (n t) (hn t ht').1
      s hs' t ht' hst.1 (hn s hs').2.symm (hn t ht').2.symm hst.2.2
      (by simpa only [(hn t ht').2] using hst.2.1)
    exact ⟨N, Q, hN, H.choice, hN, hst.1, H, hpacket⟩
  have hregion := (hR E S hbase (hsmall.trans (min_le_right _ _))).2.1
  have hcompat (a : ℝ) (ha : a ∈ times) (b : ℝ) (_hb : b ∈ times)
      (c : ℝ) (hc : c ∈ times)
      (N Q W T : EpsilonNeck (E.flow.metric E.time)) (_hab : R a b) (_hbc : R b c)
      (H₀ : edge a N b Q) (H₁ : edge b W c T) : Q = W := by
    have ha' := htimes a ha
    have hc' := htimes c hc
    have hNε : N.epsilon = epsilon := by
      have h := (S.cover.neck_epsilon (n a) (hn a ha').1).trans S.cover_epsilon
      rcases H₀.1 with hN | hN <;> simpa only [hN, reversed_epsilon] using h
    have hNU : N.carrier ⊆ S.source_region.carrier := by
      have hsub : (n a).carrier ⊆ S.source_region.carrier :=
        fun _ hx => hregion ⟨n a, (hn a ha').1, hx⟩
      rcases H₀.1 with hN | hN <;> simpa only [hN, reversed_carrier] using hsub
    exact source_edge_orientations_agree H₀.2.2.1 H₁.2.2.1 H₁.1
      (by
        rw [hNε]
        exact ((hsmall.trans (min_le_left _ _)).trans hEsmall).trans (by norm_num))
      hNU (S.lower_pos.le.trans ha'.1) H₀.2.1
      (hc'.2.trans S.upper_lt_one.le) S.path_smooth S.source_region.path_mem
      S.source_region.finite_length S.source_region.minimizing
  obtain ⟨q, hmap, hchoice, hqchain⟩ :=
    List.exists_consistent_lift times choice R edge hchain hvertex hedge hcompat
  have hmem (p : ℝ × EpsilonNeck (E.flow.metric E.time)) (hp : p ∈ q) :
      p.1 ∈ times := by
    rw [← hmap]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  have hqne : q ≠ [] := by
    intro hnil
    simp only [hnil, List.map_nil] at hmap
    change ([] : List ℝ) = S.lower :: tail at hmap
    cases hmap
  refine ⟨{ nodes := q
            nonempty := hqne
            head_time := ?_
            terminal := ?_
            vertex := ?_
            edges := ?_
            covers := ?_ }⟩
  · cases q with
    | nil => exact False.elim (hqne rfl)
    | cons p ps => exact (List.cons.inj hmap).1
  · have hlasttime : (q.getLast hqne).1 =
        (S.lower :: tail).getLast (List.cons_ne_nil _ _) := by
      have hmne : q.map Prod.fst ≠ [] := by
        rw [hmap]
        exact List.cons_ne_nil _ _
      simpa only [hmap] using
        (List.getLast_map (f := Prod.fst) (l := q) hmne).symm
    intro t ht
    have hx := hlast (show t ∈ Icc
      ((S.lower :: tail).getLast (List.cons_ne_nil _ _)) S.upper from
        by simpa only [← hlasttime] using ht)
    rcases hchoice (q.getLast hqne) (List.getLast_mem hqne) with h | h <;>
      simpa only [h, reversed_carrier, hlasttime] using hx
  · intro p hp
    have hs := htimes p.1 (hmem p hp)
    refine ⟨hs, n p.1, (hn p.1 hs).1, hchoice p hp, ?_⟩
    have hcenter := (hn p.1 hs).2.symm
    rcases hchoice p hp with h | h <;> simpa only [h, reversed_center] using hcenter
  · apply hqchain.imp_of_mem_imp
    intro p q hp hq hpq
    exact ⟨hpq.2.1, n q.1, (hn q.1 (htimes q.1 (hmem q hq))).1, hpq.2.2⟩
  · intro t ht
    obtain ⟨s, hs, hx⟩ := hcover ht
    have hs' : s ∈ q.map Prod.fst := hmap.symm ▸ hs
    obtain ⟨p, hp, hps⟩ := List.mem_map.mp hs'
    refine ⟨p, hp, ?_⟩
    have hx' : S.path t ∈ (n p.1).carrier := by simpa only [hps] using hx
    rcases hchoice p hp with h | h <;> simpa only [h, reversed_carrier] using hx'

end PoincareConjecture.M28
