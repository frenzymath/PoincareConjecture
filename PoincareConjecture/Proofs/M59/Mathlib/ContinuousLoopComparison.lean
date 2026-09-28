import PoincareConjecture.Proofs.M59.Mathlib.CircleFreeClasses
import PoincareConjecture.Proofs.M59.Mathlib.LoopTranspose
import PoincareConjecture.Proofs.M59.Mathlib.CubicalPostcomposition










set_option autoImplicit false

open scoped Topology unitInterval

noncomputable section

namespace PoincareConjecture.Proofs.M59.CubeBoundaryQuotient

open PoincareConjecture.Proofs.M02

variable {N S X : Type*} [DecidableEq N] [Nonempty N]
  [TopologicalSpace S] [T2Space S] [LocallyCompactSpace S] [TopologicalSpace X]
  (q : CubeBoundaryQuotient (Fin 1) S) (x : X)

omit [DecidableEq N] [Nonempty N] in


theorem transpose_map_descend
    (F : GenLoop N (GenLoop (Fin 1) X x) GenLoop.const) :
    GenLoop.transpose (mapGenLoop q.descendMap q.descend_const F) =
      q.descend (GenLoop.swapNested F) := by
  ext z v
  obtain ⟨w, rfl⟩ := q.surjective z
  change q.descend (F v) (q.map w) = q.descend (GenLoop.swapNested F) (q.map w) v
  rw [q.descend_map, q.descend_map]
  rfl

omit [DecidableEq N] in


theorem homotopyGroupMap_descend_injective :
    Function.Injective (homotopyGroupMap N q.descendMap
      (q.descend_const (x := x))) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro F G h
  have hFG : GenLoop.Homotopic (mapGenLoop q.descendMap q.descend_const F)
      (mapGenLoop q.descendMap q.descend_const G) := Quotient.exact h
  have ht := GenLoop.transpose_homotopic hFG
  rw [q.transpose_map_descend x, q.transpose_map_descend x] at ht
  have hs := q.homotopic_of_descend_homotopic
    (HomotopyGroup.fundamentalGroup_genLoop_mul_comm x) ht
  have hh : GenLoop.Homotopic F G := by
    simpa only [GenLoop.swapNested_swapNested] using GenLoop.swapNested_homotopic hs
  exact Quotient.sound hh

omit [DecidableEq N] [Nonempty N] in


theorem homotopyGroupMap_descend_surjective
    (hpi : Subsingleton (HomotopyGroup N X x)) :
    Function.Surjective (homotopyGroupMap N q.descendMap
      (q.descend_const (x := x))) := by
  let : PathConnectedSpace (GenLoop N X x) := GenLoop.pathConnectedSpace_of_subsingleton hpi
  intro a
  refine Quotient.inductionOn a ?_
  intro F
  obtain ⟨b, hb⟩ := q.exists_based_descend (GenLoop.transpose F)
    (PathConnectedSpace.somePath _ GenLoop.const)
  let G := GenLoop.swapNested b
  have ht : (GenLoop.transpose F).Homotopic
      (GenLoop.transpose (mapGenLoop q.descendMap q.descend_const G)) := by
    rw [q.transpose_map_descend x, GenLoop.swapNested_swapNested]
    exact hb
  exact ⟨⟦G⟧, Quotient.sound (GenLoop.homotopic_iff_transpose_homotopic.mpr ht).symm⟩



def continuousLoopEquiv (hpi : Subsingleton (HomotopyGroup N X x)) :
    HomotopyGroup N (GenLoop (Fin 1) X x) GenLoop.const ≃*
      HomotopyGroup N C(S, X) (ContinuousMap.const S x) :=
  MulEquiv.ofBijective (homotopyGroupMapHom (N := N) q.descendMap q.descend_const)
    ⟨q.homotopyGroupMap_descend_injective x, q.homotopyGroupMap_descend_surjective x hpi⟩

end PoincareConjecture.Proofs.M59.CubeBoundaryQuotient
