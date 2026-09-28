import PoincareConjecture.Proofs.M76.Mathlib.EvenGraphCycles










set_option autoImplicit false

open Set

namespace SimpleGraph

variable {V : Type*} [Finite V]





theorem exists_cycle_graph_decomposition (G : SimpleGraph V)
    (heven : ∀ v, Even (G.neighborSet v).ncard) :
    ∃ S : Finset (SimpleGraph V),
      (∀ H ∈ S, H.IsCycles ∧ H ≠ ⊥ ∧ H ≤ G) ∧
      (S : Set (SimpleGraph V)).Pairwise Disjoint ∧
      (∀ v w, G.Adj v w ↔ ∃ H ∈ S, H.Adj v w) := by
  classical
  let := Fintype.ofFinite V
  generalize hn : G.edgeFinset.card = n
  induction n using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hG : G = ⊥
    · subst G
      exact ⟨∅, by simp, by simp, by simp⟩
    obtain ⟨v, p, hp⟩ := G.exists_cycle_of_even_neighbors hG heven
    let H := p.toSubgraph.spanningCoe
    have hH : H.IsCycles := hp.isCycles_spanningCoe_toSubgraph
    have hHG : H ≤ G := p.toSubgraph.spanningCoe_le
    have hHne : H ≠ ⊥ := by
      have htwo : (H.neighborSet v).ncard = 2 :=
        hp.ncard_neighborSet_toSubgraph_eq_two p.start_mem_support
      intro hbot
      rw [hbot, neighborSet_bot, Set.ncard_empty] at htwo
      omega
    have hlt : G \ H < G := by
      refine lt_of_le_of_ne sdiff_le ?_
      intro heq
      obtain ⟨a, b, hab⟩ := ne_bot_iff_exists_adj.mp hHne
      have hres : (G \ H).Adj a b := heq.symm ▸ hHG hab
      exact hres.2 hab
    have hcount : (G \ H).edgeFinset.card < n := by
      rw [← hn]
      exact Finset.card_lt_card (edgeFinset_strict_mono hlt)
    obtain ⟨S, hS, hdisj, hcover⟩ := ih (G \ H).edgeFinset.card hcount
      (G \ H) (G.even_neighbors_sdiff_of_isCycles H hHG heven hH)
      (by simp only [edgeFinset_card, ← Nat.card_eq_fintype_card])
    have hHd (J : SimpleGraph V) (hJ : J ∈ S) : Disjoint H J := by
      apply SimpleGraph.disjoint_left.mpr
      intro a b hab hJab
      exact ((hS J hJ).2.2 hJab).2 hab
    refine ⟨insert H S, ?_, ?_, ?_⟩
    · intro J hJ
      rcases Finset.mem_insert.mp hJ with rfl | hJ
      · exact ⟨hH, hHne, hHG⟩
      · exact ⟨(hS J hJ).1, (hS J hJ).2.1, (hS J hJ).2.2.trans sdiff_le⟩
    · intro J hJ L hL hne
      rcases Finset.mem_insert.mp hJ with rfl | hJ <;>
        rcases Finset.mem_insert.mp hL with rfl | hL
      · exact (hne rfl).elim
      · exact hHd L hL
      · exact (hHd J hJ).symm
      · exact hdisj hJ hL hne
    · intro a b
      constructor
      · intro hab
        by_cases hHab : H.Adj a b
        · exact ⟨H, Finset.mem_insert_self _ _, hHab⟩
        · obtain ⟨J, hJ, hJab⟩ := (hcover a b).mp ⟨hab, hHab⟩
          exact ⟨J, Finset.mem_insert_of_mem hJ, hJab⟩
      · rintro ⟨J, hJ, hJab⟩
        rcases Finset.mem_insert.mp hJ with rfl | hJ
        · exact hHG hJab
        · exact ((hS J hJ).2.2 hJab).1





theorem IsCycles.support_inter_subset_singleton {G H J : SimpleGraph V} (q : V)
    (hdegree : ∀ v, v ≠ q → (G.neighborSet v).ncard = 2)
    (hHG : H ≤ G) (hJG : J ≤ G) (hH : H.IsCycles)
    (hdisj : Disjoint H J) : H.support ∩ J.support ⊆ {q} := by
  intro v hv
  by_contra hvq
  have hne : v ≠ q := hvq
  obtain ⟨a, ha⟩ := H.mem_support.mp hv.1
  obtain ⟨b, hb⟩ := J.mem_support.mp hv.2
  have hsub : H.neighborSet v ⊆ G.neighborSet v := fun _ hw => hHG hw
  have heq : H.neighborSet v = G.neighborSet v :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hdegree v hne, hH ⟨a, ha⟩])
  have hbH : H.Adj v b := by
    change b ∈ H.neighborSet v
    rw [heq]
    exact hJG hb
  exact SimpleGraph.disjoint_left.mp hdisj v b hbH hb

end SimpleGraph
