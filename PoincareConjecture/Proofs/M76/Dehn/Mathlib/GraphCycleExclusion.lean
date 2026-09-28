import PoincareConjecture.Proofs.M76.Dehn.Mathlib.GraphWalkPaths
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.WhiskeredLoopSplit

set_option autoImplicit false

namespace SimpleGraph.Walk

variable {V X : Type*} [TopologicalSpace X] {G : SimpleGraph V}

theorem exists_excluded_realized_cycle (a : V → X)
    (edge : ∀ {u v : V}, G.Adj u v → _root_.Path (a u) (a v))
    (hreverse : ∀ {u v : V} (h : G.Adj u v), (edge h.symm).Homotopic (edge h).symm)
    {b : X} (J : Subgroup (FundamentalGroup X b))
    {v : V} (w : G.Walk v v) (p : _root_.Path b (a v))
    (houtside : p.whiskeredLoopClass (realizePath a edge w) ∉ J) :
    ∃ (u : V) (c : G.Walk u u) (q : _root_.Path b (a u)),
      c.IsCycle ∧ q.whiskeredLoopClass (realizePath a edge c) ∉ J := by
  classical
  have main : ∀ (n : ℕ) (v : V) (w : G.Walk v v), w.length = n →
      ∀ p : _root_.Path b (a v), p.whiskeredLoopClass (realizePath a edge w) ∉ J →
        ∃ (u : V) (c : G.Walk u u) (q : _root_.Path b (a u)),
          c.IsCycle ∧ q.whiskeredLoopClass (realizePath a edge c) ∉ J := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v w hn p hw
      by_cases hshort : w.length < 3
      · exfalso
        apply hw
        change ((Path.Homotopic.Quotient.mk p).trans
          (Path.Homotopic.Quotient.mk (realizePath a edge w))).trans
          (Path.Homotopic.Quotient.mk p).symm ∈ J
        rw [realizePath_short_closed a edge hreverse w hshort,
          Path.Homotopic.Quotient.trans_refl, Path.Homotopic.Quotient.trans_symm]
        exact J.one_mem
      by_cases hcycle : w.IsCycle
      · exact ⟨v, w, p, hcycle, hw⟩
      cases w with
      | nil => simp only [length_nil] at hshort; omega
      | cons h t =>
        have ht : ¬t.IsPath := by
          intro ht
          apply hcycle
          apply isCycle_iff_isPath_tail_and_le_length.mpr
          refine ⟨?_, by omega⟩
          rw [tail_cons]
          exact (isPath_copy t _ _).mpr ht
        have hclosed : ∃ (u : V) (q : G.Walk u u), q.IsSubwalk t ∧ ¬q.Nil := by
          by_contra hnone
          apply ht
          apply isPath_iff_isSubwalk_imp_nil.mpr
          intro u q hq
          by_contra hnonempty
          exact hnone ⟨u, q, hq, hnonempty⟩
        obtain ⟨u, q, ⟨left, right, heq⟩, hq⟩ := hclosed
        subst t
        let first := cons h left
        have hqn : q.length < n := by
          simp only [length_cons, length_append] at hn
          omega
        have hremaining : (first.append right).length < n := by
          have hpositive := not_nil_iff_lt_length.mp hq
          simp only [length_cons, length_append] at hn
          dsimp [first]
          simp only [length_append]
          omega
        change p.whiskeredLoopClass
          (realizePath a edge ((first.append q).append right)) ∉ J at hw
        have hsplit : p.whiskeredLoopClass
            (((realizePath a edge first).trans (realizePath a edge q)).trans
              (realizePath a edge right)) ∉ J := by
          simpa only [Path.whiskeredLoopClass, Path.Homotopic.Quotient.mk_trans,
            realizePath_append] using hw
        rcases Path.whiskeredLoopClass_split_excluded J p
            (realizePath a edge first) (realizePath a edge q)
            (realizePath a edge right) hsplit with hqout | hremainingout
        · exact ih q.length hqn u q rfl (p.trans (realizePath a edge first)) hqout
        · apply ih (first.append right).length hremaining v (first.append right) rfl p
          simpa only [Path.whiskeredLoopClass, Path.Homotopic.Quotient.mk_trans,
            realizePath_append] using hremainingout
  exact main w.length v w rfl p houtside

end SimpleGraph.Walk
