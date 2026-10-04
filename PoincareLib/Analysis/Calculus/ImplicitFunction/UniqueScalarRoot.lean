import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
# Smoothness of uniquely specified scalar roots

The implicit function theorem gives a local smooth root. Uniqueness in
an open interval identifies it with an already specified global root,
without a separate continuity assumption on that root.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace Poincare.Analysis

/-- Unique roots with nonzero derivative depend smoothly on their parameters.
This applies to hitting times at a transverse section. -/
theorem contDiff_unique_scalar_root
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
    {f : P × ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {J : Set ℝ} (hJ : IsOpen J) {τ d : P → ℝ} {c : ℝ}
    (hmem : ∀ p, τ p ∈ J) (hvalue : ∀ p, f (p, τ p) = c)
    (hderiv : ∀ p, HasDerivAt (fun t => f (p, t)) (d p) (τ p))
    (hd : ∀ p, d p ≠ 0)
    (hunique : ∀ p t, t ∈ J → f (p, t) = c → t = τ p) :
    ContDiff ℝ ∞ τ := by
  rw [contDiff_iff_contDiffAt]
  intro p
  have hc := hf.contDiffAt (x := (p, τ p))
  have hinv : (fderiv ℝ f (p, τ p) ∘L ContinuousLinearMap.inr ℝ P ℝ).IsInvertible := by
    have heq := ((hf.differentiable (by simp) (p, τ p)).hasFDerivAt.comp
      (τ p) (hasFDerivAt_prodMk_right p (τ p))).unique (hderiv p).hasFDerivAt
    rw [heq]
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := (d p)⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · ext
      simp [smul_eq_mul, hd p]
    · ext
      simp [smul_eq_mul, hd p]
  let ψ : P → ℝ := hc.implicitFunction (by simp) hinv
  have hψ : ContDiffAt ℝ ∞ ψ p := hc.contDiffAt_implicitFunction (by simp) hinv
  have hψp : ψ p = τ p := hc.implicitFunction_apply_self (by simp) hinv
  have hψJ : ∀ᶠ q in 𝓝 p, ψ q ∈ J :=
    hψ.continuousAt.preimage_mem_nhds (hψp ▸ hJ.mem_nhds (hmem p))
  apply hψ.congr_of_eventuallyEq
  filter_upwards [hψJ, hc.eventually_apply_implicitFunction (by simp) hinv] with q hq heq
  exact (hunique q (ψ q) hq (heq.trans (hvalue p))).symm

end Poincare.Analysis
