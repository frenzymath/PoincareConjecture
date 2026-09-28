import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Matching

set_option autoImplicit false

open Set

namespace SimpleGraph

variable {V : Type*} [Finite V]

theorem exists_longest_path_from (G : SimpleGraph V) (a : V) :
    ∃ (b : V) (p : G.Walk a b), p.IsPath ∧
      ∀ (c : V) (r : G.Walk a c), r.IsPath → r.length ≤ p.length := by
  classical
  let := Fintype.ofFinite G.edgeSet
  let s : Set ℕ := {n | ∃ (b : V) (p : G.Walk a b), p.IsPath ∧ p.length = n}
  have hs : s.Finite := (finite_le_nat G.edgeFinset.card).subset
    (fun _ ⟨_, _, hp, hn⟩ => hn ▸ hp.isTrail.length_le_card_edgeFinset)
  obtain ⟨_, ⟨⟨b, p, hp, rfl⟩, hmax⟩⟩ :=
    hs.exists_maximal ⟨0, a, Walk.nil, by simp⟩
  refine ⟨b, p, hp, ?_⟩
  intro c r hr
  have h := hmax (show r.length ∈ s from ⟨c, r, hr, rfl⟩)
  omega

theorem exists_spanning_path_from_leaf (G : SimpleGraph V) (hconn : G.Connected)
    (hdegree : ∀ v, (G.neighborSet v).ncard ≤ 2) {a : V}
    (ha : (G.neighborSet a).ncard = 1) :
    ∃ (b : V) (p : G.Walk a b), p.IsPath ∧ ¬p.Nil ∧
      (∀ v, v ∈ p.support) ∧ ∀ v w, G.Adj v w ↔ p.toSubgraph.Adj v w := by
  classical
  obtain ⟨b, p, hp, hmax⟩ := G.exists_longest_path_from a
  obtain ⟨z, hz⟩ := ncard_eq_one.mp ha
  have haz : G.Adj a z := hz.symm.subset (mem_singleton z)
  have hpos : 0 < p.length := by
    have h := hmax z haz.toWalk (Walk.IsPath.of_adj haz)
    have : 1 ≤ p.length := by simpa using h
    omega
  have hnil : ¬p.Nil := Walk.not_nil_iff_lt_length.mpr hpos
  have hstart : p.toSubgraph.neighborSet a = G.neighborSet a := by
    apply eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset a)
    rw [hp.neighborSet_toSubgraph_startpoint hnil, ncard_singleton, ha]
  have hinternal (i : ℕ) (hi : i ≠ 0) (hil : i < p.length) :
      p.toSubgraph.neighborSet (p.getVert i) = G.neighborSet (p.getVert i) := by
    apply eq_of_subset_of_ncard_le (p.toSubgraph.neighborSet_subset _)
    rw [hp.ncard_neighborSet_toSubgraph_internal_eq_two hi hil]
    exact hdegree _
  have hend (w : V) (hw : G.Adj b w) : w ∈ p.support := by
    by_contra hwp
    have h := hmax w (p.concat hw) (hp.concat hwp hw)
    simp only [Walk.length_concat] at h
    omega
  have hclosed (v w : V) (hv : v ∈ p.support) (hvw : G.Adj v w) :
      w ∈ p.support := by
    obtain ⟨i, rfl, hi⟩ := Walk.mem_support_iff_exists_getVert.mp hv
    by_cases hi0 : i = 0
    · have hwa : G.Adj a w := by simpa only [hi0, Walk.getVert_zero] using hvw
      exact p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert
        (show p.toSubgraph.Adj a w from hstart.symm.subset hwa).symm)
    by_cases hil : i = p.length
    · exact hend w (by simpa only [hil, Walk.getVert_length] using hvw)
    have hwpath : p.toSubgraph.Adj (p.getVert i) w :=
      (hinternal i hi0 (by omega)).symm.subset hvw
    exact p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert hwpath.symm)
  have hall (v : V) : v ∈ p.support := by
    have hreach := (G.reachable_iff_reflTransGen a v).mp (hconn a v)
    induction hreach with
    | refl => exact p.start_mem_support
    | tail _ h ih => exact hclosed _ _ ih h
  have hnonend (v w : V) (hv : v ≠ b) (hvw : G.Adj v w) :
      p.toSubgraph.Adj v w := by
    obtain ⟨i, rfl, hi⟩ := Walk.mem_support_iff_exists_getVert.mp (hall v)
    by_cases hi0 : i = 0
    · simpa only [hi0, Walk.getVert_zero] using
        (show p.toSubgraph.Adj a w from hstart.symm.subset
          (show G.Adj a w by simpa only [hi0, Walk.getVert_zero] using hvw))
    have hil : i < p.length := by
      by_contra h
      exact hv (by rw [show i = p.length by omega, Walk.getVert_length])
    exact (hinternal i hi0 hil).symm.subset hvw
  refine ⟨b, p, hp, hnil, hall, ?_⟩
  intro v w
  constructor
  · intro hvw
    by_cases hv : v = b
    · subst v
      exact (hnonend w b hvw.ne.symm hvw.symm).symm
    · exact hnonend v w hv hvw
  · exact p.toSubgraph.adj_sub

omit [Finite V] in

theorem Walk.IsPath.ncard_neighbors_eq_one_iff_endpoints {G : SimpleGraph V} {a b : V}
    {p : G.Walk a b} (hp : p.IsPath) (hnil : ¬p.Nil)
    (hall : ∀ v, v ∈ p.support)
    (hadj : ∀ v w, G.Adj v w ↔ p.toSubgraph.Adj v w) (v : V) :
    (G.neighborSet v).ncard = 1 ↔ v = a ∨ v = b := by
  have hset (w : V) : G.neighborSet w = p.toSubgraph.neighborSet w :=
    Set.ext (fun z => hadj w z)
  constructor
  · intro hv
    by_contra h
    push Not at h
    obtain ⟨i, rfl, hi⟩ := Walk.mem_support_iff_exists_getVert.mp (hall v)
    have hi0 : i ≠ 0 := by
      intro hi0
      exact h.1 (by rw [hi0, Walk.getVert_zero])
    have hil : i < p.length := by
      by_contra hil
      exact h.2 (by rw [show i = p.length by omega, Walk.getVert_length])
    rw [hset, hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hil] at hv
    omega
  · rintro (rfl | rfl)
    · rw [hset, hp.neighborSet_toSubgraph_startpoint hnil, ncard_singleton]
    · rw [hset, hp.neighborSet_toSubgraph_endpoint hnil, ncard_singleton]

theorem exists_linear_labels_from_leaf_with_endpoints
    (G : SimpleGraph V) (hconn : G.Connected)
    (hdegree : ∀ v, (G.neighborSet v).ncard ≤ 2) {a : V}
    (ha : (G.neighborSet a).ncard = 1) :
    ∃ (n : ℕ) (e : Fin (n + 2) ≃ V), e 0 = a ∧ (∀ v w,
      G.Adj v w ↔ ∃ i : Fin (n + 1),
        (e i.castSucc = v ∧ e i.succ = w) ∨
        (e i.castSucc = w ∧ e i.succ = v)) ∧
      ∀ v, (G.neighborSet v).ncard = 1 ↔ v = e 0 ∨ v = e (Fin.last (n + 1)) := by
  obtain ⟨b, p, hp, hnil, hall, hadj⟩ :=
    G.exists_spanning_path_from_leaf hconn hdegree ha
  let n := p.length - 1
  have hlength : n + 1 = p.length :=
    Nat.sub_add_cancel (Walk.not_nil_iff_lt_length.mp hnil)
  let f : Fin (n + 2) → V := fun i => p.getVert i.val
  have hfi : Function.Injective f := by
    intro i j h
    apply Fin.ext
    exact hp.getVert_injOn (by change i.val ≤ p.length; omega)
      (by change j.val ≤ p.length; omega) h
  have hfs : Function.Surjective f := by
    intro v
    obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.mp (hall v)
    exact ⟨⟨i, by omega⟩, hi⟩
  let e : Fin (n + 2) ≃ V := Equiv.ofBijective f ⟨hfi, hfs⟩
  refine ⟨n, e, p.getVert_zero, ?_, ?_⟩
  · intro v w
    rw [hadj v w, p.toSubgraph_adj_iff]
    constructor
    · rintro ⟨i, hi, hil⟩
      exact ⟨⟨i, by omega⟩, Sym2.eq_iff.mp hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i.val, Sym2.eq_iff.mpr hi, by omega⟩
  · intro v
    change (G.neighborSet v).ncard = 1 ↔
      v = p.getVert 0 ∨ v = p.getVert (n + 1)
    rw [hlength, Walk.getVert_zero, Walk.getVert_length]
    exact hp.ncard_neighbors_eq_one_iff_endpoints hnil hall hadj v

theorem exists_linear_labels_from_leaf (G : SimpleGraph V) (hconn : G.Connected)
    (hdegree : ∀ v, (G.neighborSet v).ncard ≤ 2) {a : V}
    (ha : (G.neighborSet a).ncard = 1) :
    ∃ (n : ℕ) (e : Fin (n + 2) ≃ V), e 0 = a ∧ ∀ v w,
      G.Adj v w ↔ ∃ i : Fin (n + 1),
        (e i.castSucc = v ∧ e i.succ = w) ∨
        (e i.castSucc = w ∧ e i.succ = v) := by
  obtain ⟨n, e, he0, he, _⟩ :=
    G.exists_linear_labels_from_leaf_with_endpoints hconn hdegree ha
  exact ⟨n, e, he0, he⟩

end SimpleGraph
