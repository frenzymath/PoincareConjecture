/- Adapted from Mapher `PoincareMT/Proofs/M03/Existence/EuclideanLocalIntegrationByPartsNative.lean` at
f927d9e1f0810042766d3b5f64d3f4da02ee93cc. See
`references/ricci-flow/mapher/local-theory/port.json`. -/

import PoincareLib.Analysis.Parabolic.Quasilinear.Euclidean.Cutoff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Actual local integration by parts against compact smooth tests

Compact cutoff products supply integrability for a scalar known smooth
only on an open coordinate domain. The derivative-support property keeps
every term inside that same domain.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory Set Filter LineDeriv
open scoped Topology SchwartzMap LineDeriv ContDiff

noncomputable section

namespace PoincareMT.EuclideanDerivativeNative

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem integrable_local_mul_schwartz (η : 𝓢(E, ℝ)) (hη : HasCompactSupport η)
    {U : Set E} (hU : IsOpen U) (hηU : tsupport η ⊆ U)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f U) : Integrable (fun x => f x * η x) volume := by
  apply ((cutoffSchwartz η hη hU hηU f hf).integrable (μ := volume)).congr
  exact Eventually.of_forall (fun x => by rw [cutoffSchwartz_apply, mul_comm])

theorem hasCompactSupport_schwartzLineDeriv (η : 𝓢(E, ℝ)) (hη : HasCompactSupport η) (v : E) :
    HasCompactSupport (∂_{v} η : 𝓢(E, ℝ)) :=
  hη.of_isClosed_subset (isClosed_tsupport _) (SchwartzMap.tsupport_lineDerivOp_subset v η)

/-- No smoothness or integrability outside the compact test support is required. -/
theorem local_integral_mul_fderiv (η : 𝓢(E, ℝ)) (hη : HasCompactSupport η)
    {U : Set E} (hU : IsOpen U) (hηU : tsupport η ⊆ U)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f U) (v : E) :
    (∫ x, f x * fderiv ℝ η x v) = -(∫ x, fderiv ℝ f x v * η x) := by
  have hdf : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x v) U :=
    (hf.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const
  have hf'g : Integrable (fun x => fderiv ℝ f x v * η x) volume :=
    integrable_local_mul_schwartz η hη hU hηU hdf
  have hfg' : Integrable (fun x => f x * fderiv ℝ η x v) volume :=
    integrable_local_mul_schwartz (∂_{v} η) (hasCompactSupport_schwartzLineDeriv η hη v)
      hU ((SchwartzMap.tsupport_lineDerivOp_subset v η).trans hηU) hf
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg'
    (integrable_local_mul_schwartz η hη hU hηU hf)
    (fun x hx => (hf.contDiffAt (hU.mem_nhds (hηU hx))).differentiableAt (by simp))
    (fun _ _ => η.differentiableAt)

/-- The exact local coefficient adjoint formula before division by a density. -/
theorem local_integral_mul_fderiv_cutoff (η : 𝓢(E, ℝ)) (hη : HasCompactSupport η)
    {U : Set E} (hU : IsOpen U) (hηU : tsupport η ⊆ U)
    {f a : E → ℝ} (hf : ContDiffOn ℝ ∞ f U) (ha : ContDiffOn ℝ ∞ a U) (v : E) :
    (∫ x, f x * (η x * fderiv ℝ a x v + a x * fderiv ℝ η x v)) =
      -(∫ x, fderiv ℝ f x v * (η x * a x)) := by
  let θ : 𝓢(E, ℝ) := cutoffSchwartz η hη hU hηU a ha
  have hθ : HasCompactSupport θ := hη.mul_right (f' := a)
  have hθU : tsupport θ ⊆ U := tsupport_mul_subset_left.trans hηU
  calc
    _ = ∫ x, f x * fderiv ℝ θ x v := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      exact congrArg (fun r : ℝ => f x * r) (fderiv_cutoff_mul η hU hηU ha x v).symm
    _ = -(∫ x, fderiv ℝ f x v * θ x) := local_integral_mul_fderiv θ hθ hU hθU hf v
    _ = _ := rfl

end PoincareMT.EuclideanDerivativeNative
