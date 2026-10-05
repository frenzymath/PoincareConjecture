import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.SingularLift
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.DiscreteSingular
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# Lifted simplices in a literal product covering

A product trivialization whose first coordinate is the actual covering
projection identifies the lifted simplicial model with copies of its base
model. The fiber label is the actual second coordinate, which is constant
on each continuous simplex because the fiber is discrete.
Source: Hatcher, Propositions 1.30 and 1.34, and Theorem 2.27.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial MonoidalCategory

universe u

namespace PoincareMT.Proofs.M59

variable {E X F : Type u} [TopologicalSpace E] [TopologicalSpace X]
  [TopologicalSpace F] [DiscreteTopology F]
  (p : C(E, X)) (A : SSet.{u}) (χ : A ⟶ TopCat.toSSet.obj (TopCat.of X))
  (e : E ≃ₜ X × F) (he : ∀ z, p z = (e z).1)

/-- The actual constant fiber coordinate of a lifted singular simplex.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
def singularLiftFiberLabel (n : SimplexCategoryᵒᵖ)
    (z : (singularLiftSSet p A χ).obj n) : F :=
  (e ((TopCat.of E).toSSetObjEquiv n z.val.2 (stdSimplex.vertex 0))).2

/-- Reconstruct a literal singular lift using the product trivialization
and a retained fiber label. Source: Hatcher, Theorem 2.27. -/
def singularTrivialLift (n : SimplexCategoryᵒᵖ) (a : A.obj n) (b : F) :
    (TopCat.toSSet.obj (TopCat.of E)).obj n :=
  ((TopCat.of E).toSSetObjEquiv n).symm
    ((⟨e.symm, e.symm.continuous⟩ : C(X × F, E)).comp
      (((TopCat.of X).toSSetObjEquiv n (χ.app n a)).prodMk (ContinuousMap.const _ b)))

include he in
omit [DiscreteTopology F] in
/-- The reconstructed simplex projects to the original characteristic
simplex. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem singularTrivialLift_projection (n : SimplexCategoryᵒᵖ) (a : A.obj n) (b : F) :
    (TopCat.toSSet.map (TopCat.ofHom p)).app n (singularTrivialLift A χ e n a b) =
      χ.app n a := by
  apply ((TopCat.of X).toSSetObjEquiv n).injective
  ext t
  change p (e.symm (((TopCat.of X).toSSetObjEquiv n (χ.app n a) t), b)) = _
  rw [he, e.apply_symm_apply]

/-- The actual lifted simplicial model of a product covering is the
product of the base model and its constant fiber labels.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
def singularLiftTrivializationIso : singularLiftSSet p A χ ≅
    (SimplicialObject.const (Type u)).obj F ⊗ A where
  hom := {
    app n := ↾fun z => (show F × A.obj n from
      (singularLiftFiberLabel p A χ e n z, z.val.1))
    naturality {n m} f := by
      apply ConcreteCategory.hom_ext
      intro z
      apply Prod.ext
      · change (e ((TopCat.of E).toSSetObjEquiv n z.val.2
          (stdSimplex.map f.unop (stdSimplex.vertex 0)))).2 =
          (e ((TopCat.of E).toSSetObjEquiv n z.val.2 (stdSimplex.vertex 0))).2
        exact discreteSimplex_eq F
          ⟨fun t => (e ((TopCat.of E).toSSetObjEquiv n z.val.2 t)).2,
            continuous_snd.comp (e.continuous.comp
              ((TopCat.of E).toSSetObjEquiv n z.val.2).continuous)⟩ _ _
      · rfl }
  inv := {
    app n := ↾fun (z : F × A.obj n) => ⟨(z.2, singularTrivialLift A χ e n z.2 z.1),
      singularTrivialLift_projection p A χ e he n z.2 z.1⟩
    naturality {n m} f := by
      apply ConcreteCategory.hom_ext
      intro z
      apply Subtype.ext
      change (A.map f z.2, singularTrivialLift A χ e m (A.map f z.2) z.1) =
        (A.map f z.2, (TopCat.toSSet.obj (TopCat.of E)).map f
          (singularTrivialLift A χ e n z.2 z.1))
      apply Prod.ext
      · rfl
      apply ((TopCat.of E).toSSetObjEquiv m).injective
      ext t
      have h := congrArg (fun a => (TopCat.of X).toSSetObjEquiv m a t)
        (NatTrans.naturality_apply χ f z.2)
      exact congrArg (fun x => e.symm (x, z.1)) h }
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    change (z.val.1, singularTrivialLift A χ e n z.val.1
      (singularLiftFiberLabel p A χ e n z)) = z.val
    apply Prod.ext
    · rfl
    apply ((TopCat.of E).toSSetObjEquiv n).injective
    ext t
    apply e.injective
    change e (e.symm (_, singularLiftFiberLabel p A χ e n z)) =
      e ((TopCat.of E).toSSetObjEquiv n z.val.2 t)
    rw [e.apply_symm_apply]
    apply Prod.ext
    · have h := congrArg (fun a => (TopCat.of X).toSSetObjEquiv n a t) z.property
      exact h.symm.trans (he _)
    · exact discreteSimplex_eq F
        ⟨fun t => (e ((TopCat.of E).toSSetObjEquiv n z.val.2 t)).2,
          continuous_snd.comp (e.continuous.comp
            ((TopCat.of E).toSSetObjEquiv n z.val.2).continuous)⟩ _ _
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro z
    apply Prod.ext
    · change (e (e.symm (_, z.1))).2 = z.1
      rw [e.apply_symm_apply]
    · rfl

end PoincareMT.Proofs.M59
