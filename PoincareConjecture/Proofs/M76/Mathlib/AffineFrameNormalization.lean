import PoincareConjecture.Proofs.M76.Mathlib.SecantTransversality

set_option autoImplicit false

open Set
open scoped ContDiff

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def frameNormalize (J : F →L[ℝ] E) (Q0 Q : E →L[ℝ] F) : E →L[ℝ] F :=
  Q + (ContinuousLinearMap.id ℝ F - Q.comp J).comp Q0

theorem rightInverse_frameNormalize (J : F →L[ℝ] E) (Q0 : E →L[ℝ] F)
    (h0 : Function.RightInverse J Q0) (Q : E →L[ℝ] F) :
    Function.RightInverse J (frameNormalize J Q0 Q) := by
  intro x
  change Q (J x) + (Q0 (J x) - Q (J (Q0 (J x)))) = x
  rw [h0 x]
  abel

theorem frameNormalize_eq_self (J : F →L[ℝ] E) (Q0 Q : E →L[ℝ] F)
    (hQ : Function.RightInverse J Q) : frameNormalize J Q0 Q = Q := by
  ext x
  change Q x + (Q0 x - Q (J (Q0 x))) = Q x
  rw [hQ (Q0 x), sub_self, add_zero]

theorem contDiff_frameNormalize (J : F →L[ℝ] E) (Q0 : E →L[ℝ] F) (n : ℕ∞ω) :
    ContDiff ℝ n (frameNormalize J Q0) :=
  contDiff_id.add ((contDiff_const.sub (contDiff_id.clm_comp contDiff_const)).clm_comp
    contDiff_const)

end ContinuousLinearMap

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem isOpen_frameNormalize_transverse (J : F →L[ℝ] E) (Q0 : E →L[ℝ] F)
    (h0 : Function.RightInverse J Q0) (S : Set E) :
    IsOpen {Q : E →L[ℝ] F | (frameNormalize J Q0 Q).ker.IsSecantTransverse S} := by
  let g : (E →L[ℝ] F) → {Q : E →L[ℝ] F // Function.Surjective Q} := fun Q =>
    ⟨frameNormalize J Q0 Q, (rightInverse_frameNormalize J Q0 h0 Q).surjective⟩
  have hg : Continuous g := (contDiff_frameNormalize J Q0 0).continuous.subtype_mk _
  have hc : Continuous (fun Q : E →L[ℝ] F =>
      (⟨(frameNormalize J Q0 Q).ker⟩ : Geometry.EuclideanSubspace E)) := by
    rw [Geometry.EuclideanSubspace.continuous_iff_projector]
    change Continuous (fun Q => (g Q).val.ker.starProjection)
    exact continuous_kernel_starProjection.comp hg
  exact (Geometry.EuclideanSubspace.isOpen_isSecantTransverse S).preimage hc

end ContinuousLinearMap
