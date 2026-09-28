import PoincareConjecture.Proofs.M59.Mathlib.CubeBoundaryConnected
import PoincareConjecture.Proofs.M59.Mathlib.CubicalPostcomposition
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Algebra.Module.LocallyConvex











set_option autoImplicit false

open Set
open scoped Topology unitInterval

universe u v w

namespace IsCoveringMap

open PoincareConjecture.Proofs.M02 PoincareConjecture.Proofs.M59

variable {E : Type u} {X : Type v} {N : Type w}
  [TopologicalSpace E] [TopologicalSpace X] {p : E → X}




theorem exists_genLoop_lift [Finite N] [Nontrivial N] (hp : IsCoveringMap p)
    (e : E) (f : GenLoop N X (p e)) :
    ∃ g : GenLoop N E e, mapGenLoop ⟨p, hp.continuous⟩ rfl g = f := by
  let : ContractibleSpace (I^N) := Cube.contractibleSpace N
  let : LocallyPathConnectedSpace I := (convex_Icc (0 : ℝ) 1).locallyPathConnectedSpace
  let z : I^N := fun _ => 0
  have hz : z ∈ Cube.boundary N :=
    ⟨Classical.choice (inferInstance : Nonempty N), Or.inl rfl⟩
  obtain ⟨F, hF, _⟩ := hp.existsUnique_continuousMap_lifts f.val z e
    (GenLoop.boundary f z hz).symm
  have hproj (v : I^N) : p (F v) = f v := congrFun hF.2 v
  have hboundary (v : I^N) (hv : v ∈ Cube.boundary N) : F v = e := by
    let : PreconnectedSpace (Cube.boundary N) :=
      isPreconnected_iff_preconnectedSpace.mp
        (Cube.isPathConnected_boundary (N := N)).isConnected.isPreconnected
    have h := hp.const_of_comp (F.continuous.comp continuous_subtype_val)
      (fun a b : Cube.boundary N =>
        ((hproj a).trans (GenLoop.boundary f a a.2)).trans
          ((hproj b).trans (GenLoop.boundary f b b.2)).symm)
      (⟨v, hv⟩ : Cube.boundary N) ⟨z, hz⟩
    exact h.trans hF.1
  refine ⟨⟨F, hboundary⟩, ?_⟩
  apply Subtype.ext
  exact ContinuousMap.ext hproj




theorem homotopyGroupMap_injective [Nonempty N] (hp : IsCoveringMap p) (e : E) :
    Function.Injective (homotopyGroupMap N ⟨p, hp.continuous⟩ (rfl : p e = p e)) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro f g h
  apply Quotient.sound
  let z : I^N := fun _ => 0
  have hz : z ∈ Cube.boundary N :=
    ⟨Classical.choice (inferInstance : Nonempty N), Or.inl rfl⟩
  apply (hp.homotopicRel_iff_comp
    ⟨z, hz, (GenLoop.boundary f z hz).trans (GenLoop.boundary g z hz).symm⟩).mpr
  exact Quotient.exact h



theorem homotopyGroupMap_surjective [Finite N] [Nontrivial N]
    (hp : IsCoveringMap p) (e : E) :
    Function.Surjective (homotopyGroupMap N ⟨p, hp.continuous⟩ (rfl : p e = p e)) := by
  intro a
  refine Quotient.inductionOn a ?_
  intro f
  obtain ⟨g, hg⟩ := hp.exists_genLoop_lift e f
  exact ⟨⟦g⟧, congrArg (fun k => (⟦k⟧ : HomotopyGroup N X (p e))) hg⟩



noncomputable def homotopyGroupEquiv [Finite N] [Nontrivial N] [DecidableEq N]
    (hp : IsCoveringMap p) (e : E) : HomotopyGroup N E e ≃* HomotopyGroup N X (p e) :=
  MulEquiv.ofBijective (homotopyGroupMapHom ⟨p, hp.continuous⟩ rfl)
    ⟨hp.homotopyGroupMap_injective e, hp.homotopyGroupMap_surjective e⟩



@[simp] theorem homotopyGroupEquiv_apply [Finite N] [Nontrivial N] [DecidableEq N]
    (hp : IsCoveringMap p) (e : E) (a : HomotopyGroup N E e) :
    hp.homotopyGroupEquiv e a = homotopyGroupMap N ⟨p, hp.continuous⟩ rfl a := rfl

end IsCoveringMap
