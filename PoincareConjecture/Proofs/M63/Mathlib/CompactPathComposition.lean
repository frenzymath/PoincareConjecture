import PoincareConjecture.Proofs.M03.Existence.ContinuousPathCompositionNative
import Mathlib.Analysis.Normed.Operator.LinearIsometry










set_option autoImplicit false

universe u v w

namespace PoincareConjecture.M63




theorem contDiff_postcomp_independent_universes
    (K : Type w) [TopologicalSpace K] [CompactSpace K]
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ∞} (f : C(E, F)) (hf : ContDiff ℝ k (f : E → F)) :
    ContDiff ℝ k (fun g : C(K, E) => f.comp g) := by
  let e : ULift.{v} E ≃L[ℝ] E := ContinuousLinearEquiv.ulift
  let d : ULift.{u} F ≃L[ℝ] F := ContinuousLinearEquiv.ulift
  let f' : C(ULift.{v} E, ULift.{u} F) :=
    ⟨fun x => d.symm (f (e x)), d.symm.continuous.comp (f.continuous.comp e.continuous)⟩
  have hf' : ContDiff ℝ k (f' : ULift.{v} E → ULift.{u} F) :=
    d.symm.contDiff.comp (hf.comp e.contDiff)
  let up : C(K, E) →L[ℝ] C(K, ULift.{v} E) :=
    e.symm.toContinuousLinearMap.compLeftContinuous ℝ K
  let down : C(K, ULift.{u} F) →L[ℝ] C(K, F) :=
    d.toContinuousLinearMap.compLeftContinuous ℝ K
  have h := down.contDiff.comp
    ((ContinuousPathCompositionNative.contDiff_postcomp_of_order K f' hf').comp up.contDiff)
  convert h using 1
  funext g
  apply ContinuousMap.ext
  intro x
  change f (g x) = d (d.symm (f (e (e.symm (g x)))))
  rw [e.apply_symm_apply, d.apply_symm_apply]

end PoincareConjecture.M63
