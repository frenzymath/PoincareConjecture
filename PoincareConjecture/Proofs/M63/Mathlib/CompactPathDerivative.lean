import PoincareConjecture.Proofs.M03.Existence.DeTurckParameterBackgroundNative
import Mathlib.Analysis.Normed.Operator.LinearIsometry










set_option autoImplicit false

open Set
open scoped Topology

universe u v





theorem hasDerivAt_compact_curry
    {K : Type v} [TopologicalSpace K] [CompactSpace K]
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set ℝ} (hU : IsOpen U) (f g : ℝ → C(K, E))
    {x : ℝ} (hx : x ∈ U) (hg : ContinuousAt g x)
    (hf : ∀ y ∈ U, ∀ k : K, HasDerivAt (fun r => f r k) (g y k) y) :
    HasDerivAt f (g x) x := by
  let e : ULift.{u} ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.ulift
  let B : E →L[ℝ] (ULift.{u} ℝ →L[ℝ] E) :=
    ((ContinuousLinearMap.compL ℝ (ULift.{u} ℝ) ℝ E).flip
      e.toContinuousLinearMap).comp
        (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := E)).toContinuousLinearMap
  let A : ULift.{u} ℝ → C(K, ULift.{u} ℝ →L[ℝ] E) :=
    fun p => B.compLeftContinuous ℝ K (g (e p))
  have hA : ContinuousAt A (e.symm x) := by
    have hge : ContinuousAt g (e (e.symm x)) := by
      simpa only [e.apply_symm_apply] using hg
    exact (B.compLeftContinuous ℝ K).continuous.continuousAt.comp
      (hge.comp e.continuous.continuousAt)
  have hpoint (p : ULift.{u} ℝ) (hp : p ∈ e ⁻¹' U) (k : K) :
      HasFDerivAt (fun r => f (e r) k) (A p k) p := by
    exact (hf (e p) hp k).hasFDerivAt.comp p e.toContinuousLinearMap.hasFDerivAt
  have h := PoincareConjecture.DeTurckParameterBackgroundNative.hasFDerivAt_compact_curry
    (hU.preimage e.continuous) (fun p => f (e p)) A
    (show e.symm x ∈ e ⁻¹' U by simpa only [mem_preimage, e.apply_symm_apply] using hx)
    hA hpoint
  have hcomp := (h.comp x e.symm.toContinuousLinearMap.hasFDerivAt).hasDerivAt
  simp only [Function.comp_def] at hcomp
  have hmap : (fun p : ℝ => f (e (e.symm p))) = f := by
    funext p
    rw [e.apply_symm_apply]
  rw [hmap] at hcomp
  have hval : (((PoincareConjecture.ContinuousPathCompositionNative.pointwiseOperator K
      (A (e.symm x))).comp (ContinuousLinearMap.const ℝ K)).comp
        e.symm.toContinuousLinearMap) 1 = g x := by
    apply ContinuousMap.ext
    intro k
    change e (e.symm 1) • g (e (e.symm x)) k = g x k
    rw [e.apply_symm_apply, e.apply_symm_apply, one_smul]
  rw [hval] at hcomp
  exact hcomp
