import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ComplementaryTriangleGraph
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.OriginalGraphEdges











set_option autoImplicit false

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {ι : Type*} (A : PreAbstractSimplicialComplex ι)



theorem triangle_shared_edge_unique (q r : Triangle A) (hqr : q ≠ r)
    (e f : Edge A) (heq : e.val ⊆ q.val) (her : e.val ⊆ r.val)
    (hfq : f.val ⊆ q.val) (hfr : f.val ⊆ r.val) : e = f := by
  classical
  have hne : q.val ∩ r.val ≠ q.val := by
    intro h
    have hsub : q.val ⊆ r.val := by
      intro x hx
      rw [← h] at hx
      exact (Finset.mem_inter.mp hx).2
    apply hqr
    apply Subtype.ext
    exact Finset.eq_of_subset_of_card_le hsub (by rw [q.property.2, r.property.2])
  have hlt := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, hne⟩)
  have hcard : (q.val ∩ r.val).card ≤ 2 := by rw [q.property.2] at hlt; omega
  have he : e.val = q.val ∩ r.val := Finset.eq_of_subset_of_card_le
    (fun x hx => Finset.mem_inter.mpr ⟨heq hx, her hx⟩)
    (by rw [e.property.2]; exact hcard)
  have hf : f.val = q.val ∩ r.val := Finset.eq_of_subset_of_card_le
    (fun x hx => Finset.mem_inter.mpr ⟨hfq hx, hfr hx⟩)
    (by rw [f.property.2]; exact hcard)
  exact Subtype.ext (he.trans hf.symm)



theorem exists_unique_complementary_shared_edge (T : SimpleGraph ι)
    (s : (complementaryTriangleGraph A T).edgeSet) :
    ∃! e : Edge A, ¬edgeInGraph A T e ∧ ∀ q ∈ s.val, e.val ⊆ q.val := by
  rcases s with ⟨s, hs⟩
  induction s using Sym2.ind with
  | h q r =>
    obtain ⟨hqr, e, he, heq, her⟩ := (complementaryTriangleGraph A T).mem_edgeSet.mp hs
    refine ⟨e, ⟨he, ?_⟩, ?_⟩
    · intro t ht
      rcases Sym2.mem_iff.mp ht with rfl | rfl
      · exact heq
      · exact her
    · intro f hf
      exact triangle_shared_edge_unique A q r hqr f e
        (hf.2 q (Sym2.mem_mk_left q r)) (hf.2 r (Sym2.mem_mk_right q r)) heq her

variable [Fintype ι]

open Classical in


theorem complementary_edge_cofaces (T : SimpleGraph ι)
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2)
    (s : (complementaryTriangleGraph A T).edgeSet) (e : Edge A)
    (hshare : ∀ q ∈ s.val, e.val ⊆ q.val) : triangleCofaces A e = s.val.toFinset := by
  rcases s with ⟨s, hs⟩
  induction s using Sym2.ind with
  | h q r =>
    have hqr := ((complementaryTriangleGraph A T).mem_edgeSet.mp hs).1
    rw [Sym2.toFinset_mk_eq]
    exact triangleCofaces_eq_pair_of_distinct A (fun e => (hcofaces e).le) e q r hqr
      (hshare q (Sym2.mem_mk_left q r)) (hshare r (Sym2.mem_mk_right q r))



noncomputable def complementaryTriangleEdgeEquiv (T : SimpleGraph ι)
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2) :
    (complementaryTriangleGraph A T).edgeSet ≃ {e : Edge A // ¬edgeInGraph A T e} := by
  classical
  choose f hf using fun s => (exists_unique_complementary_shared_edge A T s).exists
  let j : (complementaryTriangleGraph A T).edgeSet →
      {e : Edge A // ¬edgeInGraph A T e} := fun s => ⟨f s, (hf s).1⟩
  apply Equiv.ofBijective j
  constructor
  · intro p q hpq
    have he : f p = f q := congrArg Subtype.val hpq
    apply Subtype.ext
    apply Sym2.toFinset_injective
    rw [← complementary_edge_cofaces A T hcofaces p (f p) (hf p).2,
      ← complementary_edge_cofaces A T hcofaces q (f q) (hf q).2, he]
  · intro e
    obtain ⟨q, r, hqr, hpair⟩ := Finset.card_eq_two.mp (hcofaces e.val)
    have heq : e.val.val ⊆ q.val := (Finset.mem_filter.mp
      (show q ∈ triangleCofaces A e.val by rw [hpair]; simp)).2
    have her : e.val.val ⊆ r.val := (Finset.mem_filter.mp
      (show r ∈ triangleCofaces A e.val by rw [hpair]; simp)).2
    let s : (complementaryTriangleGraph A T).edgeSet :=
      ⟨s(q, r), (complementaryTriangleGraph A T).mem_edgeSet.mpr
        ⟨hqr, e.val, e.property, heq, her⟩⟩
    refine ⟨s, ?_⟩
    apply Subtype.ext
    exact triangle_shared_edge_unique A q r hqr (f s) e.val
      ((hf s).2 q (Sym2.mem_mk_left q r)) ((hf s).2 r (Sym2.mem_mk_right q r)) heq her



theorem card_complementary_triangle_edges (T : SimpleGraph ι)
    (hcofaces : ∀ e : Edge A, (triangleCofaces A e).card = 2) :
    Nat.card (complementaryTriangleGraph A T).edgeSet =
      Nat.card {e : Edge A // ¬edgeInGraph A T e} :=
  Nat.card_congr (complementaryTriangleEdgeEquiv A T hcofaces)

end PreAbstractSimplicialComplex.ModTwoCochains
