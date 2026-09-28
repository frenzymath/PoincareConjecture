import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ConnectedIncidenceRanks
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.OriginalGraphEdges
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas








set_option autoImplicit false

open Set
open scoped BigOperators
open PreAbstractSimplicialComplex.ModTwoCochains

namespace LinearMap



theorem finrank_le_of_relative_kernel
    {k V W : Type*} [Field k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k V] [FiniteDimensional k W]
    (F : V →ₗ[k] W) (Z B : Submodule k V) (C : Submodule k W)
    (hrel : ∀ x ∈ Z, F x ∈ C → x ∈ B) :
    Module.finrank k Z ≤ Module.finrank k B + Module.finrank k (W ⧸ C) := by
  let q : Z →ₗ[k] W ⧸ C := C.mkQ.comp (F.comp Z.subtype)
  have hker (x : LinearMap.ker q) : (x.val : V) ∈ B := by
    apply hrel x.val x.val.property
    have hx : C.mkQ (F (x.val : V)) = 0 := x.property
    exact (Submodule.Quotient.mk_eq_zero C).mp hx
  let j : LinearMap.ker q →ₗ[k] B :=
    { toFun := fun x => ⟨x.val, hker x⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : B => (z : V)) hxy
  have hdim := LinearMap.finrank_le_finrank_of_injective hj
  have hrange := (LinearMap.range q).finrank_le
  have hsum := q.finrank_range_add_finrank_ker
  omega

end LinearMap

namespace AbstractSimplicialComplex

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (A : AbstractSimplicialComplex ι)

omit [Fintype ι] in

theorem card_edges_eq_card_edgeGraph :
    Nat.card (Edge A.toPreAbstractSimplicialComplex) = Nat.card A.edgeGraph.edgeSet := by
  have hall (e : Edge A.toPreAbstractSimplicialComplex) :
      edgeInGraph A.toPreAbstractSimplicialComplex A.edgeGraph e := by
    obtain ⟨u, v, huv, he⟩ := Finset.card_eq_two.mp e.property.2
    refine ⟨u, v, ⟨huv, he ▸ e.property.1⟩, ?_⟩
    rw [he]
    ext x
    simp only [Finset.mem_insert, Finset.mem_singleton]
  exact (Nat.card_congr (Equiv.subtypeUnivEquiv hall)).symm.trans
    (A.card_original_graph_edges A.edgeGraph le_rfl).symm


theorem card_edges_eq_vertices_of_two_neighbors
    (hdegree : ∀ v, (A.edgeGraph.neighborSet v).ncard = 2) :
    Nat.card (Edge A.toPreAbstractSimplicialComplex) = Nat.card ι := by
  classical
  have hdeg (v : ι) : A.edgeGraph.degree v = 2 := by
    rw [← A.edgeGraph.card_neighborSet_eq_degree]
    simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_card] using hdegree v
  have hsum := A.edgeGraph.sum_degrees_eq_twice_card_edges
  simp only [hdeg, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  rw [A.card_edges_eq_card_edgeGraph]
  have hc : Nat.card A.edgeGraph.edgeSet = A.edgeGraph.edgeFinset.card := by
    simp only [SimpleGraph.edgeFinset_card, Nat.card_eq_fintype_card]
  rw [hc, Nat.card_eq_fintype_card]
  omega



theorem finrank_edge_quotient_eq_one_of_two_neighbors
    (hconn : A.edgeGraph.Connected)
    (hdegree : ∀ v, (A.edgeGraph.neighborSet v).ncard = 2) :
    Module.finrank (ZMod 2) ((Edge A.toPreAbstractSimplicialComplex → ZMod 2) ⧸
      LinearMap.range (vertexCoboundary A.toPreAbstractSimplicialComplex)) = 1 := by
  classical
  have h0 := (vertexCoboundary A.toPreAbstractSimplicialComplex).finrank_range_add_finrank_ker
  rw [A.finrank_ker_vertexCoboundary hconn, Module.finrank_pi] at h0
  have hq := (LinearMap.range
    (vertexCoboundary A.toPreAbstractSimplicialComplex)).finrank_quotient_add_finrank
  rw [Module.finrank_pi] at hq
  have he := A.card_edges_eq_vertices_of_two_neighbors hdegree
  simp only [Nat.card_eq_fintype_card] at he
  omega

end AbstractSimplicialComplex
