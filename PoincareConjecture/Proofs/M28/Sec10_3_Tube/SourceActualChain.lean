import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceOrientedListIndices
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCenterDistinct
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceActualLaterCuts
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceLiteralChainAssembly
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Union

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

open PoincareConjecture.EpsilonNeck

theorem exists_actual_source_balanced_chain_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 10000 : ℝ) ∧
      ∀ {epsilon C A D₀ D : ℝ} (E : SameTimeCounterexample.{u} epsilon C A D₀ D)
        (S : CounterexampleNeckSegment E),
        0 < E.flow.scalar ⟨E.time, E.basepoint⟩ → epsilon ≤ epsilon₀ →
          ∃ (L : SourceOrientedList S) (B : BalancedNeckChain (E.flow.metric E.time) epsilon),
            B.shape = ChainShape.finite 0 (L.nodes.length - 1) ∧
            B.neck = neckOfList (L.nodes.map Prod.snd) (L.nodes.head L.nonempty).2 ∧
            B.source_necks = S.cover.necks ∧ S.cover.X ⊆ B.unionOpen := by
  obtain ⟨epsilonL, hLpos, hLsmall, hL⟩ := exists_source_oriented_list_accuracy.{u}
  obtain ⟨epsilonK, hKpos, _, hK⟩ := exists_actual_later_negative_cut_accuracy.{u}
  refine ⟨min epsilonL epsilonK, lt_min hLpos hKpos,
    (min_le_left _ _).trans hLsmall, ?_⟩
  intro epsilon C A D₀ D E S hbase hsmall
  obtain ⟨L⟩ := hL E S hbase (hsmall.trans (min_le_left _ _))
  let l := L.nodes.map Prod.snd
  let fallback := (L.nodes.head L.nonempty).2
  have hactive : (Icc (0 : ℤ) (l.length - 1)).Nonempty := by
    simpa only [l, List.length_map, SourceOrientedList.active] using L.active_nonempty
  have hactive_iff (i : ℤ) : i ∈ Icc (0 : ℤ) (l.length - 1) ↔ i ∈ L.active := by
    simp only [l, List.length_map, SourceOrientedList.active]
  have hneck (i : ℤ) : neckOfList l fallback i = (L.node i).2 :=
    L.neckOfList_eq_node i
  have hsource (i : ℤ) (hi : i ∈ Icc (0 : ℤ) (l.length - 1)) :
      ∃ N ∈ S.cover.necks, (neckOfList l fallback i).SameUpToReversal N := by
    obtain ⟨N, hN, hchoice, _⟩ := L.node_provenance ((hactive_iff i).mp hi)
    refine ⟨N, hN, ?_⟩
    rw [hneck]
    rcases hchoice with h | h
    · simpa only [h] using SameUpToReversal.refl N
    · simpa only [h] using N.reversed_sameUpToReversal
  have heps (i : ℤ) (hi : i ∈ Icc (0 : ℤ) (l.length - 1)) :
      (neckOfList l fallback i).epsilon = epsilon := by
    rw [hneck]
    exact L.node_epsilon ((hactive_iff i).mp hi)
  have hedge (i : ℤ) (hi : i ∈ Icc (0 : ℤ) (l.length - 1))
      (hnext : i + 1 ∈ Icc (0 : ℤ) (l.length - 1)) :
      SourceEdgePacket (neckOfList l fallback i) (neckOfList l fallback (i + 1)) epsilon := by
    obtain ⟨_, _, _, H⟩ := L.node_edge ((hactive_iff i).mp hi)
      ((hactive_iff (i + 1)).mp hnext)
    simpa only [hneck] using H
  have hcenter_ne (i j : ℤ) (hi : i ∈ L.active) (hj : j ∈ L.active)
      (hij : i < j) : (L.node i).2.center ≠ (L.node j).2.center := by
    have hnext : i + 1 ∈ L.active := by
      change 0 ≤ i + 1 ∧ i + 1 ≤ (L.nodes.length : ℤ) - 1
      have := hi.1
      have := hj.2
      omega
    obtain ⟨_, _, H, _⟩ := L.node_edge hi hnext
    have hnextj : (L.node (i + 1)).1 ≤ (L.node j).1 := by
      by_cases h : i + 1 = j
      · simp only [h, le_refl]
      · exact (L.node_time_lt hnext hj (by omega)).le
    exact H.center_ne_later_center
      (S.lower_pos.le.trans (L.node_time_mem hi).1)
      (L.node_time_lt hi hnext (by omega)) hnextj
      ((L.node_time_mem hj).2.trans S.upper_lt_one.le)
      S.path_smooth S.source_region.path_mem S.source_region.finite_length
      S.source_region.minimizing (L.node_center hj)
  have hdistinct (i : ℤ) (hi : i ∈ Icc (0 : ℤ) (l.length - 1))
      (j : ℤ) (hj : j ∈ Icc (0 : ℤ) (l.length - 1)) (hij : i ≠ j) :
      (neckOfList l fallback i).center ≠ (neckOfList l fallback j).center := by
    rw [hneck, hneck]
    rcases lt_or_gt_of_ne hij with h | h
    · exact hcenter_ne i j ((hactive_iff i).mp hi) ((hactive_iff j).mp hj) h
    · exact (hcenter_ne j i ((hactive_iff j).mp hj) ((hactive_iff i).mp hi) h).symm
  have hcut (i : ℤ) (hi : i ∈ Icc (0 : ℤ) (l.length - 1))
      (j : ℤ) (hj : j ∈ Icc (0 : ℤ) (l.length - 1)) (hij : i < j) :
      ∃ s ∈ Ioo (-epsilon⁻¹) 0,
        Disjoint (neckOfList l fallback j).carrier
          ((neckOfList l fallback i).region (-epsilon⁻¹) s) := by
    have hA : 0 < epsilon⁻¹ := inv_pos.mpr (S.cover_epsilon ▸ S.cover.epsilon_pos)
    refine ⟨-epsilon⁻¹ / 2, ⟨by linarith, by linarith⟩, ?_⟩
    rw [hneck, hneck]
    have hi' := (hactive_iff i).mp hi
    have hj' := (hactive_iff j).mp hj
    have hnext : i + 1 ∈ L.active := by
      change 0 ≤ i + 1 ∧ i + 1 ≤ (L.nodes.length : ℤ) - 1
      have := hi'.1
      have := hj'.2
      omega
    obtain ⟨R, hR, H₀, Hpacket⟩ := L.node_edge hi' hnext
    by_cases hadj : j = i + 1
    · simpa only [hadj] using Hpacket.later_negative_cut
    · have hnext₂ : i + 2 ∈ L.active := by
        change 0 ≤ i + 2 ∧ i + 2 ≤ (L.nodes.length : ℤ) - 1
        have := hi'.1
        have := hj'.2
        omega
      obtain ⟨V, hV, H₁, _⟩ := L.node_edge hnext
        (by simpa only [add_assoc, show (1 : ℤ) + 1 = 2 by norm_num] using hnext₂)
      obtain ⟨N₀, hN₀, hNchoice, _⟩ := L.node_provenance hi'
      obtain ⟨P₀, hP₀, hPchoice, _⟩ := L.node_provenance hj'
      have htime₂ : (L.node (i + 2)).1 ≤ (L.node j).1 := by
        by_cases h : i + 2 = j
        · simp only [h, le_refl]
        · exact (L.node_time_lt hnext₂ hj' (by omega)).le
      apply hK E S hbase (hsmall.trans (min_le_right _ _)) N₀ hN₀ P₀ hP₀
        (L.node i).2 (L.node j).2 (L.node (i + 1)).2 R (L.node (i + 2)).2 V
        hNchoice hPchoice (L.node i).1 (L.node_time_mem hi')
        (L.node j).1 (L.node_time_mem hj') (L.node (i + 1)).1 (L.node (i + 2)).1
        (L.node_time_lt hi' hnext (by omega)) (L.node_time_lt hnext hnext₂ (by omega))
        htime₂ H₀ ?_ (L.node_center hj')
      simpa only [add_assoc, show (1 : ℤ) + 1 = 2 by norm_num] using H₁
  obtain ⟨B, hshape, hnecks, hsources⟩ :=
    exists_literal_source_balanced_chain_of_edge_packets l fallback epsilon hactive
      S.cover.necks hsource heps hdistinct hedge hcut
  refine ⟨L, B, by simpa only [l, List.length_map] using hshape, hnecks, hsources, ?_⟩
  rw [S.cover_set]
  rintro x ⟨t, ht, rfl⟩
  obtain ⟨p, hp, hx⟩ := L.covers ht
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hp
  let i : ℤ := k.val
  have hi : i ∈ L.active := by
    change 0 ≤ (k.val : ℤ) ∧ (k.val : ℤ) ≤ (L.nodes.length : ℤ) - 1
    have := k.isLt
    omega
  have hnode : L.node i = p := by
    change L.nodes.getD (k.val : ℤ).toNat (L.nodes.head L.nonempty) = p
    simpa only [Int.toNat_natCast] using
      (List.getD_eq_get L.nodes (L.nodes.head L.nonempty) k).trans hk
  change S.path t ∈ ⋃ j : {j // j ∈ B.shape.active}, (B.neck j.1).carrier
  refine mem_iUnion.mpr ⟨⟨i, ?_⟩, ?_⟩
  · rw [hshape]
    exact (hactive_iff i).mpr hi
  · rw [hnecks, hneck, hnode]
    exact hx

end PoincareConjecture.M28
