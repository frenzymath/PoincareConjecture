import PoincareConjecture.Proofs.M76.Mathlib.FrameProjectionFormula










set_option autoImplicit false

open Set
open scoped ContDiff

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]



theorem contDiffAt_kernelProjectionFormula (Q : E →L[ℝ] F)
    (hQ : Function.Surjective Q) {n : ℕ∞ω} :
    ContDiffAt ℝ n (kernelProjectionFormula : (E →L[ℝ] F) → E →L[ℝ] E) Q := by
  have hadj : ContDiffAt ℝ n (adjoint : (E →L[ℝ] F) → F →L[ℝ] E) Q :=
    (adjoint : (E →L[ℝ] F) ≃ₗᵢ[ℝ] (F →L[ℝ] E)).toContinuousLinearEquiv.contDiff.contDiffAt
  have hS : ContDiffAt ℝ n (fun R : E →L[ℝ] F => R.comp (adjoint R)) Q :=
    contDiffAt_id.clm_comp hadj
  have hi := (Q.isInvertible_self_comp_adjoint_of_surjective hQ).contDiffAt_map_inverse.comp Q hS
  exact contDiffAt_const.sub ((hadj.clm_comp hi).clm_comp contDiffAt_id)



theorem contDiffAt_frameProjectionFormula (J : F →L[ℝ] E) (P : E →L[ℝ] E)
    (hP : Function.Injective (perpendicularFrame J P)) {n : ℕ∞ω} :
    ContDiffAt ℝ n (frameProjectionFormula J) P := by
  have hD : ContDiffAt ℝ n (fun R : E →L[ℝ] E => ContinuousLinearMap.id ℝ E - R) P :=
    contDiffAt_const.sub contDiffAt_id
  have hA : ContDiffAt ℝ n (perpendicularFrame J) P := hD.clm_comp contDiffAt_const
  have hAdj : ContDiffAt ℝ n (fun R => adjoint (perpendicularFrame J R)) P :=
    (adjoint : (F →L[ℝ] E) ≃ₗᵢ[ℝ] (E →L[ℝ] F)).toContinuousLinearEquiv.contDiff.contDiffAt.comp P hA
  have hGram := (perpendicularFrame J P).isInvertible_adjoint_comp_self_of_injective hP
  have hi := hGram.contDiffAt_map_inverse.comp P (hAdj.clm_comp hA)
  exact (hi.clm_comp hAdj).clm_comp hD

end ContinuousLinearMap

variable {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]




theorem ContDiffOn.ker_starProjection {Q : X → E →L[ℝ] F} {U : Set X} {n : ℕ∞ω}
    (hQ : ContDiffOn ℝ n Q U) (hsurj : ∀ x ∈ U, Function.Surjective (Q x)) :
    ContDiffOn ℝ n (fun x => (Q x).ker.starProjection) U := by
  have hreg : ContDiffOn ℝ n (fun x => (Q x).kernelProjectionFormula) U :=
    fun x hx => ((Q x).contDiffAt_kernelProjectionFormula (hsurj x hx)).comp_contDiffWithinAt
      x (hQ x hx)
  exact hreg.congr (fun x hx => (Q x).starProjection_ker_eq_formula (hsurj x hx))
