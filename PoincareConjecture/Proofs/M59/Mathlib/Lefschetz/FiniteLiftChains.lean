import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.SingularLiftDimension

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace PoincareConjecture.Proofs.M59

open M02.Topology

theorem finite_nerve_degree (J : Type u) [PartialOrder J] [Finite J] (n : ℕ) :
    Finite ((nerve J) _⦋n⦌) :=
  Finite.of_injective (fun s : (nerve J) _⦋n⦌ => s.obj)
    (fun _ _ h => nerve.ext_of_isThin h)

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

theorem finiteLift_nonDegenerate [Finite J] (n : ℕ) :
    Finite ((singularLiftSSet p (nerve J) χ).nonDegenerate n) := by
  let := finite_nerve_degree J n
  let := singularLift_finite p (nerve J) χ hp n
  exact inferInstance

omit [CompactSpace E] [T2Space X] in

theorem finiteLift_normalizedChain_isZero [Fintype J] (n : ℕ)
    (hn : Fintype.card J ≤ n) :
    IsZero (((singularLiftSSet p (nerve J) χ).normalizedChainComplex
      integralCoefficient.{u}).X n) := by
  let := finite_nerve_hasDimensionLT J
  let := singularLift_hasDimensionLT p (nerve J) χ hp (Fintype.card J)
  exact (singularLiftSSet p (nerve J) χ).isZero_normalizedChainComplex_X_of_hasDimensionLT
    integralCoefficient n (Fintype.card J) hn

end PoincareConjecture.Proofs.M59
