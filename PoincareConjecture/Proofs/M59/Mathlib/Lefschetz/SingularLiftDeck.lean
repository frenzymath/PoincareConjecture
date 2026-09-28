import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.SingularLift
import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.NormalizedMapTrace

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace PoincareConjecture.Proofs.M59

open M02.Topology

variable {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
  (p : C(E, X)) (A : SSet.{u}) (χ : A ⟶ TopCat.toSSet.obj (TopCat.of X))
  (d : C(E, E)) (hd : p.comp d = p)

def singularLiftDeck : singularLiftSSet p A χ ⟶ singularLiftSSet p A χ where
  app n := ↾fun z => ⟨(z.val.1,
    (TopCat.toSSet.map (TopCat.ofHom d)).app n z.val.2), by
    have hmap : TopCat.toSSet.map (TopCat.ofHom d) ≫
        TopCat.toSSet.map (TopCat.ofHom p) = TopCat.toSSet.map (TopCat.ofHom p) := by
      rw [← Functor.map_comp]
      exact congrArg TopCat.toSSet.map (congrArg TopCat.ofHom hd)
    exact (congrArg (fun f => f.app n z.val.2) hmap).trans z.property⟩
  naturality {n m} f := by
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (TopCat.toSSet.map (TopCat.ofHom d)).app m
          ((TopCat.toSSet.obj (TopCat.of E)).map f z.val.2) =
        (TopCat.toSSet.obj (TopCat.of E)).map f
          ((TopCat.toSSet.map (TopCat.ofHom d)).app n z.val.2)
      exact NatTrans.naturality_apply (TopCat.toSSet.map (TopCat.ofHom d)) f z.val.2

theorem singularLiftDeck_projection :
    singularLiftDeck p A χ d hd ≫ singularLiftProjection p A χ =
      singularLiftProjection p A χ ≫ TopCat.toSSet.map (TopCat.ofHom d) := by
  rfl

theorem singularLiftDeck_ne (hfree : ∀ x, d x ≠ x) (n : ℕ)
    (z : (singularLiftSSet p A χ) _⦋n⦌) :
    (singularLiftDeck p A χ d hd).app _ z ≠ z := by
  intro h
  have hs := congrArg (fun z => (TopCat.of E).toSSetObjEquiv _ z.val.2
    (stdSimplex.vertex 0)) h
  exact hfree _ hs

theorem singularLiftDeck_diagonal_zero (hfree : ∀ x, d x ≠ x) (n : ℕ)
    (s : (singularLiftSSet p A χ).nonDegenerate n) :
    (normalizedIntegralChainBasis (singularLiftSSet p A χ) n).repr
      ((SSet.normalizedChainComplexMap (singularLiftDeck p A χ d hd)
        integralCoefficient).f n
        (normalizedIntegralChainBasis (singularLiftSSet p A χ) n s)) s = 0 :=
  normalizedIntegralChainMap_diagonal_zero _ n
    (fun s => singularLiftDeck_ne p A χ d hd hfree n s.val) s

theorem singularLiftDeck_alternatingTrace_zero
    [∀ n, Finite ((singularLiftSSet p A χ).nonDegenerate n)]
    (hfree : ∀ x, d x ≠ x) (N : ℕ) :
    ChainComplex.alternatingTrace
      (SSet.normalizedChainComplexMap (singularLiftDeck p A χ d hd)
        integralCoefficient.{u}) N = 0 :=
  normalizedIntegralChainMap_alternatingTrace_zero _ N
    (fun n _ s => singularLiftDeck_ne p A χ d hd hfree n s.val)

end PoincareConjecture.Proofs.M59
