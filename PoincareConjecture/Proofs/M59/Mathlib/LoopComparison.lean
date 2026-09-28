import PoincareConjecture.Proofs.M59.Mathlib.ContinuousLoopComparison
import PoincareConjecture.Proofs.M59.Mathlib.CubicalMapNaturality

set_option autoImplicit false

open scoped Topology unitInterval

noncomputable section

namespace PoincareConjecture.Proofs.M59

open PoincareConjecture.Proofs.M02

def basedLoopAdjunction {X : Type*} [TopologicalSpace X]
    (n : Nat) [Nonempty (Fin n)] (x : X) :
    HomotopyGroup.Pi n (GenLoop (Fin 1) X x) GenLoop.const ≃*
      HomotopyGroup.Pi (n + 1) X x :=
  (HomotopyGroup.cubicalAdjunction x).trans
    (HomotopyGroup.reindex x (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)))

theorem basedLoopAdjunction_naturality
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (n : Nat) [Nonempty (Fin n)] {x : X} {y : Y} (f : C(X, Y)) (h : f x = y)
    (a : HomotopyGroup.Pi n (GenLoop (Fin 1) X x) GenLoop.const) :
    basedLoopAdjunction n y
      (homotopyGroupMap (Fin n) (mapGenLoopMap (Fin 1) f h)
        (mapGenLoopMap_const (Fin 1) f h) a) =
      homotopyGroupMap (Fin (n + 1)) f h (basedLoopAdjunction n x a) := by
  refine Quotient.inductionOn a fun a => ?_
  change (⟦GenLoop.congr y finSumFinEquiv (GenLoop.genLoopGenLoopEquiv y
    (mapGenLoop (mapGenLoopMap (Fin 1) f h) (mapGenLoopMap_const (Fin 1) f h) a))⟧ :
    HomotopyGroup.Pi (n + 1) Y y) =
      ⟦mapGenLoop f h (GenLoop.congr x finSumFinEquiv (GenLoop.genLoopGenLoopEquiv x a))⟧
  rw [genLoopGenLoopEquiv_map, genLoop_congr_map]

namespace CubeBoundaryQuotient

variable {S : Type*} [TopologicalSpace S] [T2Space S] [LocallyCompactSpace S]
  (q : CubeBoundaryQuotient (Fin 1) S)

def loopHomotopyEquiv {X : Type*} [TopologicalSpace X]
    (n : Nat) [Nonempty (Fin n)] (x : X)
    (hpi : Subsingleton (HomotopyGroup.Pi n X x)) :
    HomotopyGroup.Pi n C(S, X) (ContinuousMap.const S x) ≃*
      HomotopyGroup.Pi (n + 1) X x :=
  (q.continuousLoopEquiv x hpi).symm.trans (basedLoopAdjunction n x)

theorem loopHomotopyEquiv_naturality
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (n : Nat) [Nonempty (Fin n)] {x : X} {y : Y}
    (hpiX : Subsingleton (HomotopyGroup.Pi n X x))
    (hpiY : Subsingleton (HomotopyGroup.Pi n Y y))
    (f : C(X, Y)) (h : f x = y)
    (a : HomotopyGroup.Pi n C(S, X) (ContinuousMap.const S x)) :
    q.loopHomotopyEquiv n y hpiY
      (homotopyGroupMap (Fin n) (postcomposeMap S f) (postcomposeMap_const S f h) a) =
      homotopyGroupMap (Fin (n + 1)) f h (q.loopHomotopyEquiv n x hpiX a) := by
  let DX := q.continuousLoopEquiv x hpiX
  let DY := q.continuousLoopEquiv y hpiY
  let b := DX.symm a
  let B := homotopyGroupMap (Fin n) (mapGenLoopMap (Fin 1) f h)
    (mapGenLoopMap_const (Fin 1) f h)
  have hD : DY (B b) = homotopyGroupMap (Fin n) (postcomposeMap S f)
      (postcomposeMap_const S f h) a := by
    change homotopyGroupMap (Fin n) q.descendMap q.descend_const (B b) = _
    rw [homotopyGroupMap_descend_naturality]
    change homotopyGroupMap (Fin n) (postcomposeMap S f) _ (DX (DX.symm a)) = _
    rw [DX.apply_symm_apply]
  change basedLoopAdjunction n y (DY.symm _) = _
  rw [← hD, DY.symm_apply_apply]
  exact basedLoopAdjunction_naturality n f h b

end CubeBoundaryQuotient

end PoincareConjecture.Proofs.M59
