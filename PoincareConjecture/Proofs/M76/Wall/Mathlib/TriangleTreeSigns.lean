import PoincareConjecture.Proofs.M76.Wall.Mathlib.TreeCotreeResidualEdges
import PoincareConjecture.Proofs.M76.Wall.Mathlib.TreeEdgeParity
import Mathlib.Data.Fintype.EquivFin











set_option autoImplicit false

open scoped BigOperators
open PreAbstractSimplicialComplex.ModTwoCochains

namespace AbstractSimplicialComplex



def boundaryFaceParity {V : Type*} [DecidableEq V] (number : V → ℕ)
    (s e : Finset V) : ZMod 2 :=
  ∑ v ∈ s \ e, ((s.filter (fun w => number w < number v)).card : ZMod 2)



theorem exists_triangle_boundary_parity_vertex
    {V : Type*} [DecidableEq V] (A : PreAbstractSimplicialComplex V)
    (number : V → ℕ) (q : Triangle A) (e : Edge A) (he : e.val ⊆ q.val) :
    ∃ v, q.val \ e.val = {v} ∧
      boundaryFaceParity number q.val e.val =
        ((q.val.filter (fun w => number w < number v)).card : ZMod 2) := by
  have hcard : (q.val \ e.val).card = 1 := by
    rw [Finset.card_sdiff_of_subset he, q.property.2, e.property.2]
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
  refine ⟨v, hv, ?_⟩
  simp only [boundaryFaceParity, hv, Finset.sum_singleton]

private theorem triangle_shared_edge_eq_inter
    {V : Type*} [DecidableEq V] (A : PreAbstractSimplicialComplex V)
    (q r : Triangle A) (hqr : q ≠ r) (e : Edge A)
    (heq : e.val ⊆ q.val) (her : e.val ⊆ r.val) : e.val = q.val ∩ r.val := by
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
  exact Finset.eq_of_subset_of_card_le
    (fun x hx => Finset.mem_inter.mpr ⟨heq hx, her hx⟩)
    (by rw [e.property.2]; exact hcard)




theorem exists_primal_dual_trees_with_triangle_signs
    {V : Type*} [Fintype V] [DecidableEq V] (A : AbstractSimplicialComplex V)
    (hconn : A.edgeGraph.Connected)
    (hcofaces : ∀ e : Edge A.toPreAbstractSimplicialComplex,
      (triangleCofaces A.toPreAbstractSimplicialComplex e).card = 2)
    (htri : (triangleGraph A.toPreAbstractSimplicialComplex).Connected) :
    ∃ P : SimpleGraph V, P ≤ A.edgeGraph ∧ P.IsTree ∧
      ∃ D : SimpleGraph (Triangle A.toPreAbstractSimplicialComplex),
        D ≤ complementaryTriangleGraph A.toPreAbstractSimplicialComplex P ∧ D.IsTree ∧
        ∃ L : Finset (Edge A.toPreAbstractSimplicialComplex),
          (∀ e, e ∈ L ↔
            ∃ s : (complementaryTriangleGraph A.toPreAbstractSimplicialComplex P).edgeSet,
              (complementaryTriangleEdgeEquiv A.toPreAbstractSimplicialComplex
                P hcofaces s).val = e ∧ s.val ∉ D.edgeSet) ∧
          (∀ e ∈ L, ¬edgeInGraph A.toPreAbstractSimplicialComplex P e) ∧
          Nat.card V + Nat.card (Triangle A.toPreAbstractSimplicialComplex) + L.card =
            Nat.card (Edge A.toPreAbstractSimplicialComplex) + 2 ∧
          ∃ (number : V ↪ ℕ) (root : Triangle A.toPreAbstractSimplicialComplex)
            (sigma : Triangle A.toPreAbstractSimplicialComplex → ZMod 2),
            sigma root = 0 ∧
            ∀ (q r : Triangle A.toPreAbstractSimplicialComplex), D.Adj q r →
              ∀ e : Edge A.toPreAbstractSimplicialComplex,
                e.val ⊆ q.val → e.val ⊆ r.val →
                (sigma q + boundaryFaceParity number q.val e.val) +
                  (sigma r + boundaryFaceParity number r.val e.val) = 1 := by
  classical
  obtain ⟨P, hP, hPtree, D, hD, hDtree, L, hL, hLP, hcount⟩ :=
    A.exists_primal_dual_trees_with_residual_edges hconn hcofaces htri
  let number : V ↪ ℕ :=
    ⟨fun v => (Fintype.equivFin V v).val, by
      intro u v h
      exact (Fintype.equivFin V).injective (Fin.ext h)⟩
  let weight : Sym2 (Triangle A.toPreAbstractSimplicialComplex) → ZMod 2 :=
    Sym2.lift ⟨fun q r =>
      1 + boundaryFaceParity number q.val (q.val ∩ r.val) +
        boundaryFaceParity number r.val (q.val ∩ r.val), by
      intro q r
      dsimp only
      rw [Finset.inter_comm q.val r.val]
      ac_rfl⟩
  obtain ⟨root⟩ := hDtree.connected.nonempty
  obtain ⟨sigma, hroot, hsigns⟩ := hDtree.exists_edge_parity root weight
  refine ⟨P, hP, hPtree, D, hD, hDtree, L, hL, hLP, hcount,
    number, root, sigma, hroot, ?_⟩
  intro q r hadj e heq her
  have hqr : q ≠ r := (hD hadj).1
  have he := triangle_shared_edge_eq_inter A.toPreAbstractSimplicialComplex
    q r hqr e heq her
  have hs := hsigns hadj
  change sigma q + sigma r =
    1 + boundaryFaceParity number q.val (q.val ∩ r.val) +
      boundaryFaceParity number r.val (q.val ∩ r.val) at hs
  rw [← he] at hs
  calc
    (sigma q + boundaryFaceParity number q.val e.val) +
        (sigma r + boundaryFaceParity number r.val e.val) =
      (sigma q + sigma r) +
        (boundaryFaceParity number q.val e.val + boundaryFaceParity number r.val e.val) :=
      by ac_rfl
    _ = (1 + boundaryFaceParity number q.val e.val + boundaryFaceParity number r.val e.val) +
        (boundaryFaceParity number q.val e.val + boundaryFaceParity number r.val e.val) :=
      by rw [hs]
    _ = 1 + ((boundaryFaceParity number q.val e.val + boundaryFaceParity number q.val e.val) +
        (boundaryFaceParity number r.val e.val + boundaryFaceParity number r.val e.val)) :=
      by ac_rfl
    _ = 1 := by simp only [CharTwo.add_self_eq_zero, add_zero]

end AbstractSimplicialComplex
