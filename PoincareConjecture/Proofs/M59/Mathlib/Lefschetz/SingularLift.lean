import PoincareConjecture.Proofs.M59.Mathlib.Lefschetz.FiniteNerveChains
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Topology.Homotopy.Lifting











set_option autoImplicit false

noncomputable section

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace PoincareConjecture.Proofs.M59

variable {E X : Type u} [TopologicalSpace E] [TopologicalSpace X]
  (p : C(E, X)) (A : SSet.{u}) (χ : A ⟶ TopCat.toSSet.obj (TopCat.of X))



def singularLiftSSet : SSet.{u} where
  obj n := {z : A.obj n × (TopCat.toSSet.obj (TopCat.of E)).obj n //
    (TopCat.toSSet.map (TopCat.ofHom p)).app n z.2 = χ.app n z.1}
  map {n m} f := ↾fun z => ⟨(A.map f z.val.1,
      (TopCat.toSSet.obj (TopCat.of E)).map f z.val.2), by
    dsimp only
    rw [NatTrans.naturality_apply, z.property, ← NatTrans.naturality_apply]⟩
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    exact Prod.ext (by simp) (by simp)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    exact Prod.ext (by simp) (by simp)



def singularLiftBase : singularLiftSSet p A χ ⟶ A where
  app _ := ↾fun z => z.val.1



def singularLiftProjection : singularLiftSSet p A χ ⟶
    TopCat.toSSet.obj (TopCat.of E) where
  app _ := ↾fun z => z.val.2



theorem singularLiftProjection_comp :
    singularLiftProjection p A χ ≫ TopCat.toSSet.map (TopCat.ofHom p) =
      singularLiftBase p A χ ≫ χ := by
  ext n z
  exact z.property



theorem compact_covering_fiber_finite [CompactSpace E] [T2Space X]
    (hp : IsCoveringMap p) (x : X) : Finite (p ⁻¹' {x}) := by
  let := (hp x).discreteTopology_fiber
  let : CompactSpace (p ⁻¹' {x}) := isCompact_iff_compactSpace.mp
    (isClosed_singleton.preimage p.continuous).isCompact
  exact finite_of_compact_of_discrete




def singularLiftVertex (n : ℕ) : (singularLiftSSet p A χ) _⦋n⦌ →
    Σ s : A _⦋n⦌,
      p ⁻¹' {(TopCat.of X).toSSetObjEquiv _ (χ.app _ s) (stdSimplex.vertex 0)} :=
  fun z => ⟨z.val.1, ⟨(TopCat.of E).toSSetObjEquiv _ z.val.2 (stdSimplex.vertex 0), by
    have h := congrArg (fun s => (TopCat.of X).toSSetObjEquiv _ s (stdSimplex.vertex 0))
      z.property
    exact h⟩⟩



theorem singularLiftVertex_injective (hp : IsCoveringMap p) (n : ℕ) :
    Function.Injective (singularLiftVertex p A χ n) := by
  intro z w h
  have hbase : z.val.1 = w.val.1 := congrArg Sigma.fst h
  have hpoint : (TopCat.of E).toSSetObjEquiv _ z.val.2 (stdSimplex.vertex 0) =
      (TopCat.of E).toSSetObjEquiv _ w.val.2 (stdSimplex.vertex 0) :=
    congrArg (fun z => z.2.val) h
  apply Subtype.ext
  apply Prod.ext hbase
  apply ((TopCat.of E).toSSetObjEquiv _).injective
  apply ContinuousMap.coe_injective
  apply hp.eq_of_comp_eq ((TopCat.of E).toSSetObjEquiv _ z.val.2).continuous
    ((TopCat.of E).toSSetObjEquiv _ w.val.2).continuous _ (stdSimplex.vertex 0) hpoint
  have hz := z.property
  have hw := w.property
  rw [hbase] at hz
  have heq := hz.trans hw.symm
  exact congrArg (fun s => ((TopCat.of X).toSSetObjEquiv _ s).toFun) heq



theorem singularLift_finite [CompactSpace E] [T2Space X]
    (hp : IsCoveringMap p) (n : ℕ) [Finite (A _⦋n⦌)] :
    Finite ((singularLiftSSet p A χ) _⦋n⦌) := by
  let hfinite (s : A _⦋n⦌) := compact_covering_fiber_finite p hp
    ((TopCat.of X).toSSetObjEquiv _ (χ.app _ s) (stdSimplex.vertex 0))
  exact Finite.of_injective _ (singularLiftVertex_injective p A χ hp n)

end PoincareConjecture.Proofs.M59
