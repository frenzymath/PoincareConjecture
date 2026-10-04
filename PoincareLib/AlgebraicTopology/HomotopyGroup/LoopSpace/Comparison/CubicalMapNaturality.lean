import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.CubicalAdjunction
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.CubicalPostcomposition
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.CubeBoundaryQuotient

/-!
# Naturality of cubical adjunction and circle descent

Every map here postcomposes actual representatives. The commutative squares
are verified on their pointwise values. Source: Hatcher, Section 4.1,
pp. 340-342; MT Claim 18.16, p. 430.
-/

set_option autoImplicit false

open scoped Topology unitInterval

namespace PoincareMT.Proofs.M59

open PoincareMT.Proofs.M02

variable {N P S X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

/-- Actual continuous postcomposition between based cube spaces.
Source: Hatcher, Section 4.1, pp. 340-342. -/
def mapGenLoopMap (N : Type*) (f : C(X, Y)) (h : f x = y) :
    C(GenLoop N X x, GenLoop N Y y) :=
  ⟨mapGenLoop f h,
    ((ContinuousMap.continuous_postcomp f).comp continuous_subtype_val).subtype_mk _⟩

/-- Based cube postcomposition carries the exact constant cube to the constant.
Source: Hatcher, Section 4.1, pp. 340-342. -/
theorem mapGenLoopMap_const (N : Type*) (f : C(X, Y)) (h : f x = y) :
    mapGenLoopMap N f h GenLoop.const = GenLoop.const := by ext v; exact h

/-- Actual continuous postcomposition on continuous maps from S.
Source: Hatcher, Section 4.1, pp. 340-342. -/
def postcomposeMap (S : Type*) [TopologicalSpace S] (f : C(X, Y)) : C(C(S, X), C(S, Y)) :=
  ⟨ContinuousMap.comp f, ContinuousMap.continuous_postcomp f⟩

/-- Postcomposition sends a constant map to the specified constant map.
Source: Hatcher, Section 4.1, pp. 340-342. -/
theorem postcomposeMap_const (S : Type*) [TopologicalSpace S]
    (f : C(X, Y)) (h : f x = y) :
    postcomposeMap S f (ContinuousMap.const S x) = ContinuousMap.const S y := by
  ext z
  exact h

/-- Uncurrying commutes with actual target postcomposition on cube values.
Source: Hatcher, Section 4.1, pp. 340-342. -/
theorem genLoopGenLoopEquiv_map (f : C(X, Y)) (h : f x = y)
    (a : GenLoop N (GenLoop P X x) GenLoop.const) :
    GenLoop.genLoopGenLoopEquiv y
      (mapGenLoop (mapGenLoopMap P f h) (mapGenLoopMap_const P f h) a) =
    mapGenLoop f h (GenLoop.genLoopGenLoopEquiv x a) := by ext v; rfl

/-- Reindexing commutes with target postcomposition on cube values.
Source: Hatcher, Section 4.1, pp. 340-342. -/
theorem genLoop_congr_map (e : N ≃ P) (f : C(X, Y)) (h : f x = y)
    (a : GenLoop N X x) :
    GenLoop.congr y e (mapGenLoop f h a) = mapGenLoop f h (GenLoop.congr x e a) := by
  ext v
  rfl

section Descent

variable [TopologicalSpace S] [T2Space S] (q : CubeBoundaryQuotient P S)

/-- Exact quotient descent commutes with target postcomposition.
Source: Hatcher, Section 4.1, pp. 340-342. -/
theorem descend_mapGenLoop (f : C(X, Y)) (h : f x = y) (a : GenLoop P X x) :
    q.descend (mapGenLoop f h a) = f.comp (q.descend a) := by
  ext z
  obtain ⟨v, rfl⟩ := q.surjective z
  change q.descend (mapGenLoop f h a) (q.map v) = f (q.descend a (q.map v))
  rw [q.descend_map, q.descend_map]
  rfl

/-- The two actual maps on homotopy classes commute with circle descent.
Source: MT Claim 18.16, p. 430. -/
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

end PoincareMT.Proofs.M59
