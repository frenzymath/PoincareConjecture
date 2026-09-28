import PoincareConjecture.Proofs.M09.TimeSpaceDerivative

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped ContDiff Topology
open Filter

namespace PoincareConjecture.Proofs.M09

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem fderiv_spatialSlice (f : ℝ × E → V) (s : ℝ) (y : E)
    (hf : DifferentiableAt ℝ f (s, y)) :
    fderiv ℝ (fun x : E ↦ f (s, x)) y =
      (fderiv ℝ f (s, y)).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  have h := hf.hasFDerivAt.comp y
    ((hasFDerivAt_const s y).prodMk (hasFDerivAt_id y))
  convert h.fderiv using 1 <;> ext u <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem fderiv_spatial_bilinear_apply (f : ℝ × E → E →L[ℝ] E →L[ℝ] V)
    (s : ℝ) (y u v w : E) (hf : DifferentiableAt ℝ f (s, y)) :
    fderiv ℝ (fun x : E ↦ f (s, x) v w) y u = fderiv ℝ f (s, y) (0, u) v w := by
  have hi : DifferentiableAt ℝ (fun x : E ↦ (s, x)) y :=
    (differentiableAt_const s).prodMk differentiableAt_id
  have hf' : DifferentiableAt ℝ (fun x : E ↦ f (s, x)) y := hf.comp y hi
  have hfirst := hf'.hasFDerivAt.clm_apply (hasFDerivAt_const v y)
  have hsecond := hfirst.clm_apply (hasFDerivAt_const w y)
  have h := congrArg (fun L : E →L[ℝ] V ↦ L u) hsecond.fderiv
  rw [fderiv_spatialSlice f s y hf] at h
  simpa using h

theorem fderiv_spatialPartial_apply (R : ℝ × E → ℝ) (U : Set (ℝ × E))
    (hU : IsOpen U) (hR : ContDiffOn ℝ ∞ R U) (s : ℝ) (y : E) (hz : (s, y) ∈ U)
    (v W : E) :
    let P : E → E →L[ℝ] ℝ := fun x ↦
      (fderiv ℝ R (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)
    fderiv ℝ P y v W = fderiv ℝ (fun x ↦ fderiv ℝ (fun q : E ↦ R (s, q)) x W) y v := by
  let P : E → E →L[ℝ] ℝ := fun x ↦
    (fderiv ℝ R (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)
  have hRa := hR.contDiffAt (hU.mem_nhds hz)
  have hi : ContDiffAt ℝ ∞ (fun x : E ↦ (s, x)) y :=
    contDiffAt_const.prodMk contDiffAt_id
  have hP : DifferentiableAt ℝ P y :=
    ((((hRa.fderiv_right (m := ∞) (by simp)).comp y hi).clm_comp
      contDiffAt_const).differentiableAt (by simp))
  have heq : (fun x ↦ P x W) =ᶠ[𝓝 y]
      (fun x ↦ fderiv ℝ (fun q : E ↦ R (s, q)) x W) := by
    filter_upwards [(continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
      (hU.mem_nhds hz)] with x hx
    rw [fderiv_spatialSlice R s x
      ((hR.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp))]
  have h := (hP.hasFDerivAt.clm_apply (hasFDerivAt_const W y)).congr_of_eventuallyEq heq.symm
  simpa using (congrArg (fun L : E →L[ℝ] ℝ ↦ L v) h.fderiv).symm

end PoincareConjecture.Proofs.M09
