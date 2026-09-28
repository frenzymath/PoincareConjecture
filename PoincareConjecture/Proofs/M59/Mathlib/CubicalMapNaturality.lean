import PoincareConjecture.Proofs.M59.Mathlib.CubicalAdjunction
import PoincareConjecture.Proofs.M59.Mathlib.CubicalPostcomposition
import PoincareConjecture.Proofs.M59.Mathlib.CubeBoundaryQuotient









set_option autoImplicit false

open scoped Topology unitInterval

namespace PoincareConjecture.Proofs.M59

open PoincareConjecture.Proofs.M02

variable {N P S X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}



def mapGenLoopMap (N : Type*) (f : C(X, Y)) (h : f x = y) :
    C(GenLoop N X x, GenLoop N Y y) :=
  ⟨mapGenLoop f h,
    ((ContinuousMap.continuous_postcomp f).comp continuous_subtype_val).subtype_mk _⟩



theorem mapGenLoopMap_const (N : Type*) (f : C(X, Y)) (h : f x = y) :
    mapGenLoopMap N f h GenLoop.const = GenLoop.const := by ext v; exact h



def postcomposeMap (S : Type*) [TopologicalSpace S] (f : C(X, Y)) : C(C(S, X), C(S, Y)) :=
  ⟨ContinuousMap.comp f, ContinuousMap.continuous_postcomp f⟩



theorem postcomposeMap_const (S : Type*) [TopologicalSpace S]
    (f : C(X, Y)) (h : f x = y) :
    postcomposeMap S f (ContinuousMap.const S x) = ContinuousMap.const S y := by
  ext z
  exact h



theorem genLoopGenLoopEquiv_map (f : C(X, Y)) (h : f x = y)
    (a : GenLoop N (GenLoop P X x) GenLoop.const) :
    GenLoop.genLoopGenLoopEquiv y
      (mapGenLoop (mapGenLoopMap P f h) (mapGenLoopMap_const P f h) a) =
    mapGenLoop f h (GenLoop.genLoopGenLoopEquiv x a) := by ext v; rfl



theorem genLoop_congr_map (e : N ≃ P) (f : C(X, Y)) (h : f x = y)
    (a : GenLoop N X x) :
    GenLoop.congr y e (mapGenLoop f h a) = mapGenLoop f h (GenLoop.congr x e a) := by
  ext v
  rfl

section Descent

variable [TopologicalSpace S] [T2Space S] (q : CubeBoundaryQuotient P S)



theorem descend_mapGenLoop (f : C(X, Y)) (h : f x = y) (a : GenLoop P X x) :
    q.descend (mapGenLoop f h a) = f.comp (q.descend a) := by
  ext z
  obtain ⟨v, rfl⟩ := q.surjective z
  change q.descend (mapGenLoop f h a) (q.map v) = f (q.descend a (q.map v))
  rw [q.descend_map, q.descend_map]
  rfl



theorem homotopyGroupMap_descend_naturality (f : C(X, Y)) (h : f x = y)
    (a : HomotopyGroup N (GenLoop P X x) GenLoop.const) :
    homotopyGroupMap N q.descendMap q.descend_const
      (homotopyGroupMap N (mapGenLoopMap P f h) (mapGenLoopMap_const P f h) a) =
    homotopyGroupMap N (postcomposeMap S f) (postcomposeMap_const S f h)
      (homotopyGroupMap N q.descendMap q.descend_const a) := by
  refine Quotient.inductionOn a fun a => ?_
  apply congrArg (fun b => (⟦b⟧ : HomotopyGroup N C(S, Y) (ContinuousMap.const S y)))
  ext v z
  exact ContinuousMap.congr_fun (descend_mapGenLoop q f h (a v)) z

end Descent

end PoincareConjecture.Proofs.M59
