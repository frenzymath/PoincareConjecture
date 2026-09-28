import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Analysis.Convex.Contractible

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace PoincareConjecture.Proofs.M59

variable (F : Type u) [TopologicalSpace F] [DiscreteTopology F]

theorem discreteSimplex_eq {n : ℕ} (f : C(stdSimplex ℝ (Fin (n + 1)), F))
    (x y : stdSimplex ℝ (Fin (n + 1))) : f x = f y :=
  PreconnectedSpace.constant inferInstance f.continuous

def discreteSingularEvaluation : TopCat.toSSet.obj (TopCat.of F) ⟶
    (SimplicialObject.const (Type u)).obj F where
  app n := ↾fun s => (TopCat.of F).toSSetObjEquiv n s (stdSimplex.vertex 0)
  naturality {n m} f := by
    apply ConcreteCategory.hom_ext
    intro s
    change ((TopCat.of F).toSSetObjEquiv n s)
        (stdSimplex.map f.unop (stdSimplex.vertex 0)) =
      ((TopCat.of F).toSSetObjEquiv n s) (stdSimplex.vertex 0)
    exact discreteSimplex_eq F _ _ _

def discreteSingularConstant : (SimplicialObject.const (Type u)).obj F ⟶
    TopCat.toSSet.obj (TopCat.of F) where
  app n := ↾fun a => ((TopCat.of F).toSSetObjEquiv n).symm (ContinuousMap.const _ a)
  naturality {n m} f := by
    apply ConcreteCategory.hom_ext
    intro a
    apply ((TopCat.of F).toSSetObjEquiv m).injective
    rfl

def discreteSingularIso : TopCat.toSSet.obj (TopCat.of F) ≅
    (SimplicialObject.const (Type u)).obj F where
  hom := discreteSingularEvaluation F
  inv := discreteSingularConstant F
  hom_inv_id := by
    ext n : 1
    apply ConcreteCategory.hom_ext
    intro s
    apply ((TopCat.of F).toSSetObjEquiv n).injective
    ext t
    change ((TopCat.of F).toSSetObjEquiv n s) (stdSimplex.vertex 0) =
      ((TopCat.of F).toSSetObjEquiv n s) t
    exact discreteSimplex_eq F _ _ _
  inv_hom_id := by
    rfl

end PoincareConjecture.Proofs.M59
