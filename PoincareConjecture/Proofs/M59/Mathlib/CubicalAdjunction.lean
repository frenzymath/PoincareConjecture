import PoincareConjecture.Proofs.M59.Mathlib.GenLoopTopology










set_option autoImplicit false

open scoped Topology unitInterval

noncomputable section

namespace GenLoop

variable {N P X : Type*} [TopologicalSpace X] (x : X)
  [DecidableEq N] [DecidableEq P]



theorem genLoopGenLoopEquiv_transAt (i : N)
    (f g : GenLoop N (GenLoop P X x) const) :
    genLoopGenLoopEquiv x (transAt i f g) =
      transAt (Sum.inl i) (genLoopGenLoopEquiv x f) (genLoopGenLoopEquiv x g) := by
  ext y
  have hl (s : I) : Function.update y (Sum.inl i) s ∘ Sum.inl =
      Function.update (y ∘ Sum.inl) i s := by
    funext j
    by_cases h : j = i <;> simp [h]
  have hr (s : I) : Function.update y (Sum.inl i) s ∘ Sum.inr = y ∘ Sum.inr := by
    funext j
    simp
  change (transAt i f g) (y ∘ Sum.inl) (y ∘ Sum.inr) = _
  simp only [transAt, coe_copy, Function.comp_apply]
  split_ifs
  · exact congrArg₂ (fun a b => f a b) (hl _).symm
      (hr (Set.projIcc 0 1 zero_le_one (2 * y (Sum.inl i)))).symm
  · exact congrArg₂ (fun a b => g a b) (hl _).symm
      (hr (Set.projIcc 0 1 zero_le_one (2 * y (Sum.inl i) - 1))).symm



theorem congr_transAt (e : N ≃ P) (i : N) (f g : GenLoop N X x) :
    congr x e (transAt i f g) = transAt (e i) (congr x e f) (congr x e g) := by
  ext y
  have hu (s : I) : Function.update y (e i) s ∘ e =
      Function.update (y ∘ e) i s := by
    funext j
    simp [Function.update_apply, e.injective.eq_iff]
  change (transAt i f g) (y ∘ e) =
    (transAt (e i) (congr x e f) (congr x e g)) y
  simp only [transAt, coe_copy, Function.comp_apply]
  split_ifs
  · change f _ = f _
    exact congrArg f (hu _).symm
  · change g _ = g _
    exact congrArg g (hu _).symm

end GenLoop

namespace HomotopyGroup

variable {N P X : Type*} [TopologicalSpace X] (x : X)
  [DecidableEq N] [DecidableEq P] [Nonempty N]



def cubicalAdjunction :
    HomotopyGroup N (GenLoop P X x) GenLoop.const ≃*
      HomotopyGroup (N ⊕ P) X x where
  toEquiv := equivOfGenLoopHomeomorph (GenLoop.genLoopGenLoopEquiv x)
  map_mul' a b := Quotient.inductionOn₂ a b fun f g => by
    let i : N := Classical.choice inferInstance
    exact (congrArg (equivOfGenLoopHomeomorph (GenLoop.genLoopGenLoopEquiv x))
      (HomotopyGroup.mul_spec (i := i) (p := f) (q := g))).trans
      ((congrArg (fun z => (⟦z⟧ : HomotopyGroup (N ⊕ P) X x))
        (GenLoop.genLoopGenLoopEquiv_transAt x i g f)).trans
        (HomotopyGroup.mul_spec (i := Sum.inl i)).symm)



def reindex [Nonempty P] (e : N ≃ P) :
    HomotopyGroup N X x ≃* HomotopyGroup P X x where
  toEquiv := equivOfGenLoopHomeomorph (GenLoop.congr x e)
  map_mul' a b := Quotient.inductionOn₂ a b fun f g => by
    let i : N := Classical.choice inferInstance
    exact (congrArg (equivOfGenLoopHomeomorph (GenLoop.congr x e))
      (HomotopyGroup.mul_spec (i := i) (p := f) (q := g))).trans
      ((congrArg (fun z => (⟦z⟧ : HomotopyGroup P X x))
        (GenLoop.congr_transAt x e i g f)).trans
        (HomotopyGroup.mul_spec (i := e i)).symm)

omit [DecidableEq N] in


theorem fundamentalGroup_genLoop_mul_comm
    (a b : FundamentalGroup (GenLoop N X x) GenLoop.const) : a * b = b * a := by
  classical
  let : Nontrivial (Fin 1 ⊕ N) :=
    ⟨⟨Sum.inl 0, Sum.inr (Classical.choice inferInstance), Sum.inl_ne_inr⟩⟩
  let e := (pi1MulEquivFundamentalGroup
    (X := GenLoop N X x) (x := GenLoop.const)).symm.trans
      (cubicalAdjunction (N := Fin 1) (P := N) x)
  apply e.injective
  simpa only [map_mul] using mul_comm (e a) (e b)



def squareFundamentalGroupEquivPiThree {X : Type*} [TopologicalSpace X] (x : X) :
    FundamentalGroup (GenLoop (Fin 2) X x) GenLoop.const ≃* HomotopyGroup.Pi 3 X x :=
  ((pi1MulEquivFundamentalGroup (X := GenLoop (Fin 2) X x)
    (x := GenLoop.const)).symm.trans (cubicalAdjunction x)).trans
      (reindex x (finSumFinEquiv : Fin 1 ⊕ Fin 2 ≃ Fin 3))

end HomotopyGroup
