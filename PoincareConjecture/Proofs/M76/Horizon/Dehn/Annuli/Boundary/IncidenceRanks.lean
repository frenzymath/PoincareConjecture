import PoincareConjecture.Proofs.M76.Dehn.Mathlib.BoundaryExactnessRanks
import Mathlib.LinearAlgebra.Dimension.RankNullity












set_option autoImplicit false

open PreAbstractSimplicialComplex.ModTwoCochains

namespace AbstractSimplicialComplex

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
  (K : AbstractSimplicialComplex ι) (A : AbstractSimplicialComplex κ)

local notation "KA" => K.toPreAbstractSimplicialComplex
local notation "AA" => A.toPreAbstractSimplicialComplex



theorem boundary_incidence_rank_le_of_counts (k : ℕ)
    (hconn : K.edgeGraph.Connected)
    (hrank : Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary KA)) ≤
      Module.finrank (ZMod 2) (LinearMap.range (vertexCoboundary KA)) + k)
    (htop : Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary AA).dualMap) =
      Module.finrank (ZMod 2) (LinearMap.ker (vertexCoboundary AA)))
    (hbound : Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary AA).dualMap) +
        Nat.card (Tetrahedron KA) ≤
      Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary KA).dualMap) + 1)
    (hcount : 2 * Nat.card ι + 2 * Nat.card (Triangle KA) + Nat.card (Edge AA) =
      2 * Nat.card (Edge KA) + 2 * Nat.card (Tetrahedron KA) +
        Nat.card κ + Nat.card (Triangle AA)) :
    Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary AA)) ≤
      Module.finrank (ZMod 2) (LinearMap.range (vertexCoboundary AA)) + 2 * k := by
  classical
  have hK0 := (vertexCoboundary KA).finrank_range_add_finrank_ker
  rw [K.finrank_ker_vertexCoboundary hconn, Module.finrank_pi] at hK0
  have hK1 := (edgeCoboundary KA).finrank_range_add_finrank_ker
  have hK2 := (edgeCoboundary KA).dualMap.finrank_range_add_finrank_ker
  have hA0 := (vertexCoboundary AA).finrank_range_add_finrank_ker
  have hA1 := (edgeCoboundary AA).finrank_range_add_finrank_ker
  have hA2 := (edgeCoboundary AA).dualMap.finrank_range_add_finrank_ker
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range,
    Subspace.dual_finrank_eq, Module.finrank_pi] at hK2 hA2
  rw [Module.finrank_pi] at hK1 hA0 hA1
  rw [htop] at hA2 hbound
  simp only [Nat.card_eq_fintype_card] at hcount hbound
  omega

end AbstractSimplicialComplex

namespace Submodule

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]



abbrev Subquotient (S T : Submodule F V) := S ⧸ T.comap S.subtype

theorem finrank_subquotient_le_of_finrank_le [FiniteDimensional F V]
    (S T : Submodule F V) (hTS : T ≤ S) (k : ℕ)
    (hrank : Module.finrank F S ≤ Module.finrank F T + k) :
    Module.finrank F (Subquotient S T) ≤ k := by
  have hdim := (comapSubtypeEquivOfLe hTS).finrank_eq
  have hquot := (T.comap S.subtype).finrank_quotient_add_finrank
  rw [hdim] at hquot
  change Module.finrank F (S ⧸ T.comap S.subtype) ≤ k
  omega

end Submodule

namespace PreAbstractSimplicialComplex.ModTwoCochains

variable {ι : Type*} [Fintype ι] (A : PreAbstractSimplicialComplex ι)



theorem first_chain_rank_le_of_cochain_rank_le (k : ℕ)
    (hrank : Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary A)) ≤
      Module.finrank (ZMod 2) (LinearMap.range (vertexCoboundary A)) + k) :
    Module.finrank (ZMod 2) (LinearMap.ker (vertexCoboundary A).dualMap) ≤
      Module.finrank (ZMod 2) (LinearMap.range (edgeCoboundary A).dualMap) + k := by
  classical
  have h0 := (vertexCoboundary A).dualMap.finrank_range_add_finrank_ker
  have h1 := (edgeCoboundary A).finrank_range_add_finrank_ker
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range,
    Subspace.dual_finrank_eq, Module.finrank_pi] at h0
  rw [Module.finrank_pi] at h1
  rw [LinearMap.finrank_range_dualMap_eq_finrank_range]
  omega



theorem first_chain_quotient_finrank_le_of_cochain_rank_le (k : ℕ)
    (hrank : Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary A)) ≤
      Module.finrank (ZMod 2) (LinearMap.range (vertexCoboundary A)) + k) :
    Module.finrank (ZMod 2)
      (Submodule.Subquotient (LinearMap.ker (vertexCoboundary A).dualMap)
        (LinearMap.range (edgeCoboundary A).dualMap)) ≤ k := by
  classical
  have hle : LinearMap.range (edgeCoboundary A).dualMap ≤
      LinearMap.ker (vertexCoboundary A).dualMap := by
    rintro z ⟨b, rfl⟩
    apply LinearMap.ext
    intro v
    change b (edgeCoboundary A (vertexCoboundary A v)) = 0
    rw [edgeCoboundary_vertexCoboundary, map_zero]
  exact Submodule.finrank_subquotient_le_of_finrank_le _ _ hle k
    (first_chain_rank_le_of_cochain_rank_le A k hrank)

end PreAbstractSimplicialComplex.ModTwoCochains
