import Mathlib.Analysis.Calculus.ContDiff.Operations







set_option autoImplicit false

open scoped ContDiff Topology
open Filter

namespace PoincareConjecture.Proofs.M09

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def parametricSpatialInjection : E →L[ℝ] (P × E) × ℝ :=
  ((0 : E →L[ℝ] P).prod (ContinuousLinearMap.id ℝ E)).prod 0

noncomputable def parametricSpatialCovector (C : (P × E) × ℝ → ℝ)
    (z : (P × E) × ℝ) : E →L[ℝ] ℝ :=
  (fderiv ℝ C z).comp parametricSpatialInjection

noncomputable def parametricSpatialSecond (C : (P × E) × ℝ → ℝ)
    (z : (P × E) × ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  (fderiv ℝ (parametricSpatialCovector C) z).comp parametricSpatialInjection

theorem parametricSpatialCovector_smooth (C : (P × E) × ℝ → ℝ)
    (U : Set ((P × E) × ℝ)) (hU : IsOpen U) (hC : ContDiffOn ℝ ∞ C U) :
    ContDiffOn ℝ ∞ (parametricSpatialCovector C) U :=
  (hC.fderiv_of_isOpen hU (m := ∞) (by simp)).clm_comp contDiffOn_const

theorem parametricSpatialSecond_smooth (C : (P × E) × ℝ → ℝ)
    (U : Set ((P × E) × ℝ)) (hU : IsOpen U) (hC : ContDiffOn ℝ ∞ C U) :
    ContDiffOn ℝ ∞ (parametricSpatialSecond C) U :=
  ((parametricSpatialCovector_smooth C U hU hC).fderiv_of_isOpen hU
    (m := ∞) (by simp)).clm_comp contDiffOn_const

theorem fderiv_parametric_spatial_slice (C : (P × E) × ℝ → ℝ)
    (a : P) (y : E) (t : ℝ) (hC : DifferentiableAt ℝ C ((a, y), t)) :
    fderiv ℝ (fun v ↦ C ((a, v), t)) y = parametricSpatialCovector C ((a, y), t) := by
  exact (hC.hasFDerivAt.comp y
    (((hasFDerivAt_const a y).prodMk (hasFDerivAt_id y)).prodMk
      (hasFDerivAt_const t y))).fderiv

theorem fderiv_parametric_spatial_second (C : (P × E) × ℝ → ℝ)
    (U : Set ((P × E) × ℝ)) (hU : IsOpen U) (hC : ContDiffOn ℝ ∞ C U)
    (a : P) (y : E) (t : ℝ) (hz : ((a, y), t) ∈ U) :
    fderiv ℝ (fderiv ℝ (fun v ↦ C ((a, v), t))) y =
      parametricSpatialSecond C ((a, y), t) := by
  have hi : Continuous (fun v : E ↦ ((a, v), t)) :=
    (continuous_const.prodMk continuous_id).prodMk continuous_const
  have heq : fderiv ℝ (fun v ↦ C ((a, v), t)) =ᶠ[𝓝 y]
      (fun v ↦ parametricSpatialCovector C ((a, v), t)) := by
    filter_upwards [hi.continuousAt.preimage_mem_nhds (hU.mem_nhds hz)] with v hv
    exact fderiv_parametric_spatial_slice C a v t
      ((hC.contDiffAt (hU.mem_nhds hv)).differentiableAt (by simp))
  rw [heq.fderiv_eq]
  have hD := ((parametricSpatialCovector_smooth C U hU hC).contDiffAt
    (hU.mem_nhds hz)).differentiableAt (by simp)
  have hslice : HasFDerivAt (fun v : E ↦ ((a, v), t))
      parametricSpatialInjection y :=
    ((hasFDerivAt_const a y).prodMk (hasFDerivAt_id y)).prodMk
      (hasFDerivAt_const t y)
  exact (hD.hasFDerivAt.comp y hslice).fderiv

theorem deriv_parametric_time_slice (C : (P × E) × ℝ → ℝ)
    (a : P) (y : E) (t : ℝ) (hC : DifferentiableAt ℝ C ((a, y), t)) :
    deriv (fun s ↦ C ((a, y), s)) t = fderiv ℝ C ((a, y), t) ((0, 0), 1) := by
  have h := (hC.hasFDerivAt.comp t
    ((hasFDerivAt_const (a, y) t).prodMk (hasFDerivAt_id t))).hasDerivAt
  exact h.deriv

end PoincareConjecture.Proofs.M09
