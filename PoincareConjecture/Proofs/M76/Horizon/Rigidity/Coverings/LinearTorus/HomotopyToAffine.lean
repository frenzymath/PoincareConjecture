import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.LinearTorus.Lifts.Affine
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.LinearTorus.Lifts.PeriodicDescent

set_option autoImplicit false

open Set Topology

namespace PoincareConjecture.M76.LinearTorus

variable (p : ℝ)

theorem exists_integerMatrix_decomposition
    (f : C(AddCircle p × AddCircle p, AddCircle p × AddCircle p)) :
    ∃ (A : Matrix (Fin 2) (Fin 2) ℤ) (E : C(AddCircle p × AddCircle p, ℝ × ℝ)),
      ∀ z, f z = quotientMap p (E z) + integerMatrixMap p A z := by
  let f₁ : C(AddCircle p × AddCircle p, AddCircle p) :=
    ⟨fun x => (f x).1, continuous_fst.comp f.continuous⟩
  let f₂ : C(AddCircle p × AddCircle p, AddCircle p) :=
    ⟨fun x => (f x).2, continuous_snd.comp f.continuous⟩
  obtain ⟨a, b, e₁, he₁⟩ := exists_scalar_decomposition p f₁
  obtain ⟨c, d, e₂, he₂⟩ := exists_scalar_decomposition p f₂
  let A : Matrix (Fin 2) (Fin 2) ℤ := !![a, b; c, d]
  let E : C(AddCircle p × AddCircle p, ℝ × ℝ) :=
    ⟨fun z => (e₁ z, e₂ z), e₁.continuous.prodMk e₂.continuous⟩
  refine ⟨A, E, fun z => Prod.ext ?_ ?_⟩
  · change f₁ z = (e₁ z : AddCircle p) + (a • z.1 + b • z.2)
    rw [he₁]
    abel
  · change f₂ z = (e₂ z : AddCircle p) + (c • z.1 + d • z.2)
    rw [he₂]
    abel

def homotopyToAffineOfRealError
    (f : C(AddCircle p × AddCircle p, AddCircle p × AddCircle p))
    (A : Matrix (Fin 2) (Fin 2) ℤ) (E : C(AddCircle p × AddCircle p, ℝ × ℝ))
    (h : ∀ z, f z = quotientMap p (E z) + integerMatrixMap p A z) :
    f.HomotopyRel (affineIntegerMatrixMap p A (f 0)) {0} where
  toFun z := quotientMap p (E z.2 + (z.1 : ℝ) • (E 0 - E z.2)) + integerMatrixMap p A z.2
  continuous_toFun := by fun_prop
  map_zero_left z := by simpa using (h z).symm
  map_one_left z := by
    have hzero : quotientMap p (E 0) = f 0 := by simpa using (h 0).symm
    simp [hzero, add_comm]
  prop' t z hz := by
    obtain rfl : z = 0 := Set.mem_singleton_iff.mp hz
    simpa using (h 0).symm

@[simp] theorem homotopyToAffineOfRealError_apply
    (f : C(AddCircle p × AddCircle p, AddCircle p × AddCircle p))
    (A : Matrix (Fin 2) (Fin 2) ℤ) (E : C(AddCircle p × AddCircle p, ℝ × ℝ))
    (h : ∀ z, f z = quotientMap p (E z) + integerMatrixMap p A z)
    (t : unitInterval) (x : AddCircle p × AddCircle p) :
    homotopyToAffineOfRealError p f A E h (t, x) =
      quotientMap p (E x + (t : ℝ) • (E 0 - E x)) + integerMatrixMap p A x := rfl

theorem exists_homotopy_affineIntegerMatrixMap
    (f : C(AddCircle p × AddCircle p, AddCircle p × AddCircle p)) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℤ,
      Nonempty (f.HomotopyRel (affineIntegerMatrixMap p A (f 0)) {0}) := by
  obtain ⟨A, E, h⟩ := exists_integerMatrix_decomposition p f
  exact ⟨A, ⟨homotopyToAffineOfRealError p f A E h⟩⟩

end PoincareConjecture.M76.LinearTorus
