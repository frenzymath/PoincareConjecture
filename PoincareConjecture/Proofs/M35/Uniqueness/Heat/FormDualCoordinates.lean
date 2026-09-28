import PoincareConjecture.Proofs.M03.Existence.HilbertFormBasisNative










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set

namespace PoincareConjecture.M35.Uniqueness.Heat

open HilbertResolventNative

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem form_repr_adjoint (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (u : H) (i : EigenIndex J) :
    (formEigenbasis J hc hd hi).repr (J.adjoint u) i =
      Real.sqrt i.1.val * (eigenbasis J hc hd).repr u i := by
  simp only [HilbertBasis.repr_apply_apply, formEigenbasis_apply, eigenbasis_apply,
    J.adjoint_inner_right, inclusion_formEigenvector J hc hd, real_inner_smul_left]

theorem form_repr_adjoint_inclusion (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (v : V) (i : EigenIndex J) :
    (formEigenbasis J hc hd hi).repr (J.adjoint (J v)) i =
      i.1.val * (formEigenbasis J hc hd hi).repr v i := by
  rw [form_repr_adjoint, repr_inclusion, ← mul_assoc,
    Real.mul_self_sqrt (eigenparameter_pos J hc hd i).le]

theorem form_repr_adjoint_decode (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J)
    (z : SpectralHeatNative.State (EigenIndex J)) (i : EigenIndex J) :
    (formEigenbasis J hc hd hi).repr
        (J.adjoint ((eigenbasis J hc hd).repr.symm z)) i =
      Real.sqrt i.1.val * z i := by
  rw [form_repr_adjoint, LinearIsometryEquiv.apply_symm_apply]



theorem form_variational_pairing (J : V →L[ℝ] H) (w v : V) :
    inner ℝ w (v - J.adjoint (J v)) = inner ℝ w v - inner ℝ (J w) (J v) := by
  rw [inner_sub_right, J.adjoint_inner_right]

end PoincareConjecture.M35.Uniqueness.Heat
