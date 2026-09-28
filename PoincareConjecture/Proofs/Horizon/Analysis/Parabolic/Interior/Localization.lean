import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.CompactSlices
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension









set_option autoImplicit false

open Filter Set
open scoped ContDiff Topology

namespace Poincare.Parabolic.Interior

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiff_smul_cutoff {U : Set E} (hU : IsOpen U)
    {f : E → F} (hf : ContDiffOn ℝ ∞ f U)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ U) :
    ContDiff ℝ ∞ (fun x => χ x • f x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.smul ((hf x (hsupp hx)).contDiffAt (hU.mem_nhds (hsupp hx)))
  · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp hx)] with y hy
    simp only [hy, Pi.zero_apply, zero_smul]

omit [NormedSpace ℝ E] in
theorem hasCompactSupport_smul_cutoff {χ : E → ℝ} (hχ : HasCompactSupport χ)
    (f : E → F) : HasCompactSupport (fun x => χ x • f x) :=
  hχ.smul_right

omit [NormedSpace ℝ E] in
theorem smul_cutoff_eventuallyEq {χ : E → ℝ} {x : E}
    (hχ : χ =ᶠ[𝓝 x] fun _ => 1) (f : E → F) :
    (fun y => χ y • f y) =ᶠ[𝓝 x] f := by
  filter_upwards [hχ] with y hy
  simp only [hy, one_smul]

theorem fderiv_smul_cutoff {χ : E → ℝ} {x : E}
    (hχ : χ =ᶠ[𝓝 x] fun _ => 1) (f : E → F) :
    fderiv ℝ (fun y => χ y • f y) x = fderiv ℝ f x :=
  (smul_cutoff_eventuallyEq hχ f).fderiv_eq

theorem fderiv_fderiv_smul_cutoff {χ : E → ℝ} {x : E}
    (hχ : χ =ᶠ[𝓝 x] fun _ => 1) (f : E → F) :
    fderiv ℝ (fderiv ℝ (fun y => χ y • f y)) x = fderiv ℝ (fderiv ℝ f) x :=
  ((smul_cutoff_eventuallyEq hχ f).fderiv).fderiv_eq

end Poincare.Parabolic.Interior
