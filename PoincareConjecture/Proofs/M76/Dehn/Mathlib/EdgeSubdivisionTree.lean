import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

open scoped BigOperators

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

def incidenceSubdivision : SimpleGraph (V ⊕ G.edgeSet) where
  Adj x y := match x, y with
    | Sum.inl v, Sum.inr e => v ∈ e.val
    | Sum.inr e, Sum.inl v => v ∈ e.val
    | _, _ => False
  symm := ⟨by intro x y; cases x <;> cases y <;> exact id⟩
  loopless := ⟨by intro x; cases x <;> exact id⟩

theorem reachable_incidenceSubdivision {v w : V} (h : G.Reachable v w) :
    G.incidenceSubdivision.Reachable (Sum.inl v) (Sum.inl w) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | @cons u v w huv p ih =>
    let e : G.edgeSet := ⟨s(u, v), G.mem_edgeSet.mpr huv⟩
    have hleft : G.incidenceSubdivision.Adj (Sum.inl u) (Sum.inr e) :=
      Sym2.mem_mk_left u v
    have hright : G.incidenceSubdivision.Adj (Sum.inr e) (Sum.inl v) :=
      Sym2.mem_mk_right u v
    exact hleft.reachable.trans (hright.reachable.trans ih)

theorem Connected.incidenceSubdivision (hG : G.Connected) :
    G.incidenceSubdivision.Connected := by
  let : Nonempty V := hG.nonempty
  have attached (x : V ⊕ G.edgeSet) :
      ∃ v : V, G.incidenceSubdivision.Reachable x (Sum.inl v) := by
    rcases x with v | e
    · exact ⟨v, Reachable.refl _⟩
    · have h : G.incidenceSubdivision.Adj (Sum.inr e) (Sum.inl e.val.out.1) :=
        Sym2.out_fst_mem e.val
      exact ⟨e.val.out.1, h.reachable⟩
  refine ⟨?_⟩
  intro x y
  obtain ⟨v, hx⟩ := attached x
  obtain ⟨w, hy⟩ := attached y
  exact hx.trans ((G.reachable_incidenceSubdivision (hG.preconnected v w)).trans hy.symm)

noncomputable def incidenceSubdivisionEdgeEquiv :
    (Σ e : G.edgeSet, {v : V // v ∈ e.val}) ≃ G.incidenceSubdivision.edgeSet := by
  let f : (Σ e : G.edgeSet, {v : V // v ∈ e.val}) → G.incidenceSubdivision.edgeSet :=
    fun q => ⟨s(Sum.inl q.2.val, Sum.inr q.1), G.incidenceSubdivision.mem_edgeSet.mpr q.2.property⟩
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨e, v⟩ ⟨d, w⟩ h
    have hval := congrArg Subtype.val h
    change s(Sum.inl v.val, Sum.inr e) = s(Sum.inl w.val, Sum.inr d) at hval
    rcases Sym2.eq_iff.mp hval with ⟨hvw, hed⟩ | ⟨hbad, _⟩
    · cases Sum.inr.inj hed
      have hvw' : v = w := Subtype.ext (Sum.inl.inj hvw)
      cases hvw'
      rfl
    · cases hbad
  · rintro ⟨s, hs⟩
    induction s using Sym2.ind with
    | h x y =>
      have hxy := G.incidenceSubdivision.mem_edgeSet.mp hs
      rcases x with v | e <;> rcases y with w | d
      · exact hxy.elim
      · exact ⟨⟨d, ⟨v, hxy⟩⟩, rfl⟩
      · refine ⟨⟨e, ⟨w, hxy⟩⟩, Subtype.ext ?_⟩
        exact Sym2.eq_swap
      · exact hxy.elim

theorem card_incidenceSubdivision_edges [Finite V] :
    Nat.card G.incidenceSubdivision.edgeSet = 2 * Nat.card G.edgeSet := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have hfiber (e : G.edgeSet) : Nat.card {v : V // v ∈ e.val} = 2 := by
    calc
      _ = Nat.card (e.val.toFinset : Set V) := Nat.card_congr
        (Equiv.subtypeEquivRight (fun _ => Sym2.mem_toFinset.symm))
      _ = e.val.toFinset.card := by
        simp only [Finset.coe_sort_coe, Nat.card_eq_fintype_card, Fintype.card_coe]
      _ = 2 := Sym2.card_toFinset_of_not_isDiag _ (G.not_isDiag_of_mem_edgeSet e.property)
  rw [← Nat.card_congr G.incidenceSubdivisionEdgeEquiv, Nat.card_sigma]
  simp only [hfiber, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card, Nat.mul_comm]

theorem IsTree.incidenceSubdivision [Finite V] (hG : G.IsTree) :
    G.incidenceSubdivision.IsTree := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have hcount := (isTree_iff_connected_and_card.mp hG).2
  apply isTree_iff_connected_and_card.mpr
  refine ⟨SimpleGraph.Connected.incidenceSubdivision G hG.connected, ?_⟩
  rw [G.card_incidenceSubdivision_edges, Nat.card_sum]
  omega

end SimpleGraph
