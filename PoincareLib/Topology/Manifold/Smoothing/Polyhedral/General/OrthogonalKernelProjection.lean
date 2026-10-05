import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Orthogonal projectors onto surjective kernels

The kernel of a surjective operator varies continuously in the actual
orthogonal-projector coordinates of planes. The projector is computed
as `I - Q* (Q Q*)⁻¹ Q`. This is the topology calculation for Cairns
1940, Section 4, p. 800, and Lemma 5.1, p. 801; see M76 derivation 28.
-/

set_option autoImplicit false

open Set

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- A surjective operator has invertible adjoint Gram operator on its
target, including when the target is zero-dimensional.
See Cairns p. 801 and M76 derivation 28. -/
theorem isInvertible_self_comp_adjoint_of_surjective (Q : E →L[ℝ] F)
    (hQ : Function.Surjective Q) : (Q.comp (adjoint Q)).IsInvertible := by
  have hker : (Q.comp (adjoint Q)).ker = ⊥ := by
    rw [ker_self_comp_adjoint, ← orthogonal_range,
      LinearMap.range_eq_top.mpr hQ, Submodule.top_orthogonal_eq_bot]
  have hinj : Function.Injective (Q.comp (adjoint Q)) := LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective (Q.comp (adjoint Q)) :=
    LinearMap.injective_iff_surjective.mp hinj
  exact ⟨ContinuousLinearEquiv.ofBijective (Q.comp (adjoint Q)) hker
    (LinearMap.range_eq_top.mpr hsurj), rfl⟩

/-- The totalized formula for a kernel projector. Its interpretation
as the orthogonal projector requires surjectivity.
See Cairns p. 801 and M76 derivation 28. -/
noncomputable def kernelProjectionFormula (Q : E →L[ℝ] F) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - ((adjoint Q).comp (Q.comp (adjoint Q)).inverse).comp Q

/-- The Gram formula is the geometric orthogonal projector onto the
kernel. See Cairns pp. 800--801 and M76 derivation 28. -/
theorem starProjection_ker_eq_formula (Q : E →L[ℝ] F) (hQ : Function.Surjective Q) :
    Q.ker.starProjection = Q.kernelProjectionFormula := by
  have hS := Q.isInvertible_self_comp_adjoint_of_surjective hQ
  ext x
  change Q.ker.starProjection x = x - (adjoint Q) ((Q.comp (adjoint Q)).inverse (Q x))
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · change Q (x - (adjoint Q) ((Q.comp (adjoint Q)).inverse (Q x))) = 0
    have he := hS.self_apply_inverse (Q x)
    change Q ((adjoint Q) ((Q.comp (adjoint Q)).inverse (Q x))) = Q x at he
    rw [map_sub, he, sub_self]
  · intro w hw
    have hw' : Q w = 0 := hw
    rw [sub_sub_cancel, adjoint_inner_left, hw', inner_zero_right]

/-- The projector formula is continuous at every surjective map.
Invertibility of the Gram operator is checked before invoking smooth
operator inversion. See Cairns p. 801 and M76 derivation 28. -/
theorem continuousAt_kernelProjectionFormula (Q : E →L[ℝ] F) (hQ : Function.Surjective Q) :
    ContinuousAt (kernelProjectionFormula : (E →L[ℝ] F) → E →L[ℝ] E) Q := by
  have hadj : ContinuousAt (adjoint : (E →L[ℝ] F) → F →L[ℝ] E) Q :=
    adjoint.continuous.continuousAt
  have hS : ContinuousAt (fun R : E →L[ℝ] F => R.comp (adjoint R)) Q :=
    continuousAt_id.clm_comp hadj
  have hinverse : ContinuousAt (inverse : (F →L[ℝ] F) → F →L[ℝ] F)
      (Q.comp (adjoint Q)) :=
    (Q.isInvertible_self_comp_adjoint_of_surjective hQ).contDiffAt_map_inverse
      (n := 0) |>.continuousAt
  have hi : ContinuousAt (fun R : E →L[ℝ] F => (R.comp (adjoint R)).inverse) Q :=
    hinverse.comp (f := fun R : E →L[ℝ] F => R.comp (adjoint R)) hS
  exact continuousAt_const.sub ((hadj.clm_comp hi).clm_comp continuousAt_id)

/-- Kernels vary continuously on the surjective locus in orthogonal
projector coordinates. No continuity is asserted across a rank drop.
See Cairns p. 800 and M76 derivation 28. -/
theorem continuous_kernel_starProjection :
    Continuous (fun Q : {Q : E →L[ℝ] F // Function.Surjective Q} => Q.val.ker.starProjection) := by
  have he : (fun Q : {Q : E →L[ℝ] F // Function.Surjective Q} => Q.val.ker.starProjection) =
      (fun Q => Q.val.kernelProjectionFormula) :=
    funext (fun Q => Q.val.starProjection_ker_eq_formula Q.property)
  rw [he]
  exact continuous_iff_continuousAt.mpr (fun Q =>
    (Q.val.continuousAt_kernelProjectionFormula Q.property).comp
      continuous_subtype_val.continuousAt)

end ContinuousLinearMap
