import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ConnectedIncidenceRanks
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TetrahedronIncidence
import Mathlib.LinearAlgebra.Dual.Lemmas










set_option autoImplicit false

open PreAbstractSimplicialComplex.ModTwoCochains

namespace AbstractSimplicialComplex

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
  (K : AbstractSimplicialComplex ι) (A : AbstractSimplicialComplex κ)

local notation "KA" => K.toPreAbstractSimplicialComplex
local notation "AA" => A.toPreAbstractSimplicialComplex




theorem boundary_incidence_exact_of_counts
    (hconn : K.edgeGraph.Connected)
    (hexact : LinearMap.ker (edgeCoboundary KA) = LinearMap.range (vertexCoboundary KA))
    (htop : Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary AA).dualMap) =
      Module.finrank (ZMod 2) (LinearMap.ker (vertexCoboundary AA)))
    (hbound : Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary AA).dualMap) +
        Nat.card (Tetrahedron KA) ≤
      Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary KA).dualMap) + 1)
    (hcount : 2 * Nat.card ι + 2 * Nat.card (Triangle KA) + Nat.card (Edge AA) =
      2 * Nat.card (Edge KA) + 2 * Nat.card (Tetrahedron KA) +
        Nat.card κ + Nat.card (Triangle AA)) :
    LinearMap.ker (edgeCoboundary AA) = LinearMap.range (vertexCoboundary AA) := by
  classical
  have hK := K.edge_incidence_rank_of_exact hconn hexact
  have hK2 := (edgeCoboundary KA).dualMap.finrank_range_add_finrank_ker
  have hA0 := (vertexCoboundary AA).finrank_range_add_finrank_ker
  have hA1 := (edgeCoboundary AA).finrank_range_add_finrank_ker
  have hA2 := (edgeCoboundary AA).dualMap.finrank_range_add_finrank_ker
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range,
    Subspace.dual_finrank_eq, Module.finrank_pi] at hK2 hA2
  rw [Module.finrank_pi] at hA0 hA1
  rw [htop] at hA2 hbound
  have hle : LinearMap.range (vertexCoboundary AA) ≤ LinearMap.ker (edgeCoboundary AA) := by
    rintro z ⟨a, rfl⟩
    exact edgeCoboundary_vertexCoboundary AA a
  have hdimle := Submodule.finrank_mono hle
  have heq : Module.finrank (ZMod 2) (LinearMap.range (vertexCoboundary AA)) =
      Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary AA)) := by
    simp only [Nat.card_eq_fintype_card] at hK hcount hbound
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle heq).symm



theorem boundary_chain_exact_of_incidence
    (hexact : LinearMap.ker (edgeCoboundary AA) = LinearMap.range (vertexCoboundary AA)) :
    LinearMap.range (edgeCoboundary AA).dualMap =
      LinearMap.ker (vertexCoboundary AA).dualMap := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker (edgeCoboundary AA), hexact,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range (vertexCoboundary AA)]

end AbstractSimplicialComplex
