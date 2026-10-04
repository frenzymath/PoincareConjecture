import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.SingularLiftDimension

/-!
# Bounded finite chains for a lifted finite nerve

The compact-cover fiber argument makes all lifted simplices finite, and
covering uniqueness reflects degeneracy. These two geometric facts give
the actual normalized chain model its finite free and bounded properties.
Source: Hatcher, Theorem 2.27, printed pp. 128-130.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace PoincareMT.Proofs.M59

open M02.Topology

/-- Every simplicial degree of a finite partial order's nerve is finite.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem finite_nerve_degree (J : Type u) [PartialOrder J] [Finite J] (n : ℕ) :
    Finite ((nerve J) _⦋n⦌) :=
  Finite.of_injective (fun s : (nerve J) _⦋n⦌ => s.obj)
    (fun _ _ h => nerve.ext_of_isThin h)

/-- The number of vertices bounds the nondegenerate dimension of the
finite nerve. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem finite_nerve_hasDimensionLT (J : Type u) [PartialOrder J] [Fintype J] :
    (nerve J).HasDimensionLT (Fintype.card J) where
  degenerate_eq_top n hn := by
    apply Set.eq_univ_of_forall
    intro s
    apply ((nerve J).mem_degenerate_iff_notMem_nonDegenerate s).mpr
    intro hs
    exact (Nat.not_lt_of_ge hn) (nerve_nonDegenerate_dim_lt J ⟨s, hs⟩)

variable {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
  [CompactSpace E] [T2Space X] (p : C(E, X)) (hp : IsCoveringMap p)
  (J : Type u) [PartialOrder J]
  (χ : nerve J ⟶ TopCat.toSSet.obj (TopCat.of X))

include hp

/-- The literal lifted finite nerve has finitely many nondegenerate
simplices in every degree. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem finiteLift_nonDegenerate [Finite J] (n : ℕ) :
    Finite ((singularLiftSSet p (nerve J) χ).nonDegenerate n) := by
  let := finite_nerve_degree J n
  let := singularLift_finite p (nerve J) χ hp n
  exact inferInstance

omit [CompactSpace E] [T2Space X] in
/-- The actual normalized lifted nerve complex is bounded by the number
of base vertices. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem finiteLift_normalizedChain_isZero [Fintype J] (n : ℕ)
    (hn : Fintype.card J ≤ n) :
    IsZero (((singularLiftSSet p (nerve J) χ).normalizedChainComplex
      integralCoefficient.{u}).X n) := by
  let := finite_nerve_hasDimensionLT J
  let := singularLift_hasDimensionLT p (nerve J) χ hp (Fintype.card J)
  exact (singularLiftSSet p (nerve J) χ).isZero_normalizedChainComplex_X_of_hasDimensionLT
    integralCoefficient n (Fintype.card J) hn

end PoincareMT.Proofs.M59
