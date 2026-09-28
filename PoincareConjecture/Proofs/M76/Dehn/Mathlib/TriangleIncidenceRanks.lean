import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TriangleChainKernel
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ConnectedIncidenceRanks









set_option autoImplicit false

open PreAbstractSimplicialComplex.ModTwoCochains

namespace AbstractSimplicialComplex

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (A : AbstractSimplicialComplex ι)



theorem triangle_incidence_count_of_exact
    (hconn : A.edgeGraph.Connected)
    (hexact : LinearMap.ker (edgeCoboundary A.toPreAbstractSimplicialComplex) =
      LinearMap.range (vertexCoboundary A.toPreAbstractSimplicialComplex)) :
    Nat.card ι + Nat.card (Triangle A.toPreAbstractSimplicialComplex) =
      Nat.card (Edge A.toPreAbstractSimplicialComplex) + 1 +
        Module.finrank (ZMod 2)
          (LinearMap.ker (edgeCoboundary A.toPreAbstractSimplicialComplex).dualMap) := by
  classical
  have h1 := A.edge_incidence_rank_of_exact hconn hexact
  have h2 :=
    (edgeCoboundary A.toPreAbstractSimplicialComplex).dualMap.finrank_range_add_finrank_ker
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range, Subspace.dual_finrank_eq,
    Module.finrank_pi] at h2
  simp only [Nat.card_eq_fintype_card] at h1 ⊢
  omega



theorem triangle_incidence_count_of_one_coface
    (hconn : A.edgeGraph.Connected)
    (hexact : LinearMap.ker (edgeCoboundary A.toPreAbstractSimplicialComplex) =
      LinearMap.range (vertexCoboundary A.toPreAbstractSimplicialComplex))
    (hcofaces : ∀ e : Edge A.toPreAbstractSimplicialComplex,
      (triangleCofaces A.toPreAbstractSimplicialComplex e).card ≤ 2)
    (htri : (triangleGraph A.toPreAbstractSimplicialComplex).Preconnected)
    (hne : ∃ e : Edge A.toPreAbstractSimplicialComplex,
      (triangleCofaces A.toPreAbstractSimplicialComplex e).card = 1) :
    Nat.card ι + Nat.card (Triangle A.toPreAbstractSimplicialComplex) =
      Nat.card (Edge A.toPreAbstractSimplicialComplex) + 1 := by
  have h := A.triangle_incidence_count_of_exact hconn hexact
  rw [finrank_boundary2_ker_of_one_coface _ hcofaces htri hne, add_zero] at h
  exact h



theorem triangle_incidence_count_of_two_cofaces
    (hconn : A.edgeGraph.Connected)
    (hexact : LinearMap.ker (edgeCoboundary A.toPreAbstractSimplicialComplex) =
      LinearMap.range (vertexCoboundary A.toPreAbstractSimplicialComplex))
    (hcofaces : ∀ e : Edge A.toPreAbstractSimplicialComplex,
      (triangleCofaces A.toPreAbstractSimplicialComplex e).card = 2)
    (htri : (triangleGraph A.toPreAbstractSimplicialComplex).Connected) :
    Nat.card ι + Nat.card (Triangle A.toPreAbstractSimplicialComplex) =
      Nat.card (Edge A.toPreAbstractSimplicialComplex) + 2 := by
  have h := A.triangle_incidence_count_of_exact hconn hexact
  rw [finrank_boundary2_ker_of_two_cofaces _ hcofaces htri] at h
  omega

end AbstractSimplicialComplex
