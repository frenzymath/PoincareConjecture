import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FiniteHilbertMap








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] {m : ℕ}

def finiteHilbertEquiv (e : V ≃L[ℝ] H) :
    PiLp 2 (fun _ : Fin m => V) ≃L[ℝ] PiLp 2 (fun _ : Fin m => H) :=
  { (finiteHilbertMap e.toContinuousLinearMap).toLinearMap with
    invFun := finiteHilbertMap e.symm.toContinuousLinearMap
    left_inv := by intro u; ext i; simp
    right_inv := by intro u; ext i; simp
    continuous_toFun := (finiteHilbertMap e.toContinuousLinearMap).continuous
    continuous_invFun := (finiteHilbertMap e.symm.toContinuousLinearMap).continuous }

@[simp] theorem finiteHilbertEquiv_apply (e : V ≃L[ℝ] H)
    (u : PiLp 2 (fun _ : Fin m => V)) (i : Fin m) : finiteHilbertEquiv e u i = e (u i) := rfl

theorem finiteHilbertMap_comp {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (I : H →L[ℝ] X) (E : V →L[ℝ] H) :
    finiteHilbertMap (m := m) (I.comp E) =
      (finiteHilbertMap I).comp (finiteHilbertMap E) := by
  ext u i
  rfl

end PoincareConjecture.M35.Uniqueness.Heat
