import PoincareConjecture.Proofs.M02.Topology.SingularHomotopyClasses
import PoincareConjecture.Proofs.M02.Topology.HomotopyAddition
import PoincareConjecture.Proofs.M02.Topology.SimplicialHomologyDetection

set_option autoImplicit false

open CategoryTheory Simplicial

universe u

namespace PoincareConjecture.Proofs.M02.Topology

theorem singularPointedSimplexClass_eq_of_homology_eq
    (X : TopCat.{u}) (n : Nat)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk 0)))
    (rho : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk (n + 2))) ->
      (TopCat.toSSet.obj X).PtSimplex (n + 2) x)
    (hrho : forall a : (TopCat.toSSet.obj X).PtSimplex (n + 2) x,
      rho (SSet.yonedaEquiv a.map) = a)
    (hfill : forall s :
        (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk (n + 3))),
      Exists fun F : (SSet.stdSimplex.{u}.obj (SimplexCategory.mk (n + 3))) ⟶
          TopCat.toSSet.obj X =>
        forall j : Fin (n + 4),
          SSet.stdSimplex.δ j ≫ F = (rho ((TopCat.toSSet.obj X).δ j s)).map)
    (a b : (TopCat.toSSet.obj X).PtSimplex (n + 2) x)
    (z w : ModuleCat.of Int (ULift.{u} Int) ⟶
      ((TopCat.toSSet.obj X).chainComplex
        (ModuleCat.of Int (ULift.{u} Int))).cycles (n + 2))
    (hz : z ≫ ((TopCat.toSSet.obj X).chainComplex
        (ModuleCat.of Int (ULift.{u} Int))).iCycles (n + 2) =
      (TopCat.toSSet.obj X).ιChainComplex (SSet.yonedaEquiv a.map) -
        (TopCat.toSSet.obj X).ιChainComplex
          (SSet.yonedaEquiv (SSet.const x :
            (SSet.stdSimplex.{u}.obj (SimplexCategory.mk (n + 2))) ⟶ TopCat.toSSet.obj X)))
    (hw : w ≫ ((TopCat.toSSet.obj X).chainComplex
        (ModuleCat.of Int (ULift.{u} Int))).iCycles (n + 2) =
      (TopCat.toSSet.obj X).ιChainComplex (SSet.yonedaEquiv b.map) -
        (TopCat.toSSet.obj X).ιChainComplex
          (SSet.yonedaEquiv (SSet.const x :
            (SSet.stdSimplex.{u}.obj (SimplexCategory.mk (n + 2))) ⟶ TopCat.toSSet.obj X)))
    (heq : z ≫ ((TopCat.toSSet.obj X).chainComplex
        (ModuleCat.of Int (ULift.{u} Int))).homologyπ (n + 2) =
      w ≫ ((TopCat.toSSet.obj X).chainComplex
        (ModuleCat.of Int (ULift.{u} Int))).homologyπ (n + 2)) :
    singularPointedSimplexClass X (n + 1) x a =
      singularPointedSimplexClass X (n + 1) x b := by
  let Y := TopCat.toSSet.obj X
  let : SSet.KanComplex Y := singular_kanComplex X
  let A := Additive (HomotopyGroup (Fin (n + 2)) X (TopCat.toSSetObj₀Equiv x))
  let v (c : Y.PtSimplex (n + 2) x) : A :=
    Additive.ofMul (singularPointedSimplexClass X (n + 1) x c)
  have hvzero : v SSet.RelativeMorphism.const = 0 :=
    congrArg Additive.ofMul (singularPointedSimplexClass_const X (n + 1) x)
  have hvrel (c d : Y.PtSimplex (n + 2) x) (i : Fin (n + 3))
      (r : SSet.PtSimplex.RelStruct c d i) : v c = v d :=
    congrArg Additive.ofMul (singularPointedSimplexClass_eq_of_relStruct X (n + 1) x c d i r)
  have hvmul (c d e : Y.PtSimplex (n + 2) x)
      (r : SSet.PtSimplex.MulStruct c d e (0 : Fin (n + 2))) : v e = v c + v d :=
    congrArg Additive.ofMul (singularPointedSimplexClass_mul X n x c d e r)
  have hv (s : Y.obj (Opposite.op (SimplexCategory.mk (n + 3)))) :
      (∑ j : Fin (n + 4), ((-1 : Int) ^ j.val) • v (rho (Y.δ j s))) = 0 := by
    obtain ⟨F, hF⟩ := hfill s
    exact pointedSimplex_alternating_face_sum Y n x v hvzero hvrel hvmul F
      (fun j => rho (Y.δ j s)) hF
  have h := simplicial_values_eq_of_homology_eq Y (n + 1) A
    (fun s => v (rho s)) hv (SSet.yonedaEquiv a.map) (SSet.yonedaEquiv b.map)
    (SSet.yonedaEquiv (SSet.const x :
      (SSet.stdSimplex.{u}.obj (SimplexCategory.mk (n + 2))) ⟶ Y)) z w hz hw heq
  rw [hrho, hrho] at h
  exact congrArg Additive.toMul h

end PoincareConjecture.Proofs.M02.Topology
