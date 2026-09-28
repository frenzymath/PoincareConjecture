import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularFiber.OpenSubset
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.UniversalProperty
import Mathlib.Geometry.Manifold.Diffeomorph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology

namespace Poincare.Geometry.Manifold.RegularFiber

def iteratedOpenFiberEquiv {M : Type*} [TopologicalSpace M] {k : ℕ}
    (f : M → Fin k → ℝ) (φ : M → ℝ) (U : Opens M)
    (c : Fin k → ℝ) (t : ℝ) :
    openLevelSet (φ ∘ openFiberIncl f U c) ⊤ t ≃
      openFiber (fun y => Fin.cons (α := fun _ : Fin (k + 1) => ℝ) (φ y) (f y)) U
        (Fin.cons t c) where
  toFun x := ⟨(x.val.val : U), by
    funext i
    exact Fin.cases x.property (fun j => congrFun x.val.val.property j) i⟩
  invFun x := ⟨⟨⟨x.val, by
    funext i
    exact congrFun x.property i.succ⟩, trivial⟩, congrFun x.property 0⟩
  left_inv x := rfl
  right_inv x := rfl

@[simp] theorem openFiberIncl_iteratedOpenFiberEquiv
    {M : Type*} [TopologicalSpace M] {k : ℕ}
    (f : M → Fin k → ℝ) (φ : M → ℝ) (U : Opens M)
    (c : Fin k → ℝ) (t : ℝ)
    (x : openLevelSet (φ ∘ openFiberIncl f U c) ⊤ t) :
    openFiberIncl (fun y => Fin.cons (α := fun _ : Fin (k + 1) => ℝ) (φ y) (f y)) U
      (Fin.cons t c) (iteratedOpenFiberEquiv f φ U c t x) =
        openFiberIncl f U c (openLevelIncl (φ ∘ openFiberIncl f U c) ⊤ t x) := rfl

end Poincare.Geometry.Manifold.RegularFiber
