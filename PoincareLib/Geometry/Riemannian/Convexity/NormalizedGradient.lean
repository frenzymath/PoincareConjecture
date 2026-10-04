import PoincareLib.Geometry.Riemannian.ScalarOperators.Gradient
import Mathlib.Analysis.ODE.Gronwall

/-!
# Infinitesimal contraction of normalized gradient fields

For a regular level of a smooth function, the tangential derivative of
the normalized negative gradient is minus the Hessian divided by the
squared gradient norm. This is the local calculation in Eschenburg,
Lemma 7.5, p. 521. The constants below distinguish a gradient-norm bound
from a squared-gradient-norm bound.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open PoincareMT Filter Set
open scoped ContDiff Topology Manifold Bundle

namespace Poincare.Geometry.Riemannian.Convexity

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

/-- The negative gradient rescaled so that the function decreases at unit
speed wherever its gradient is nonzero. -/
def normalizedNegGradient (D : LeviCivitaData g) (f : M → ℝ)
    (x : M) : TangentSpace (𝓡 n) x :=
  -(g.inner x (D.gradient f x) (D.gradient f x))⁻¹ • D.gradient f x

/-- The normalized gradient is smooth at regular points. -/
theorem contMDiffAt_normalizedNegGradient (D : LeviCivitaData g)
    {f : M → ℝ} {x : M} (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (hregular : g.inner x (D.gradient f x) (D.gradient f x) ≠ 0) :
    ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (T% (normalizedNegGradient D f)) x := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hgrad := D.contMDiffAt_gradient hf
  have hpair : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => g.inner y (D.gradient f y) (D.gradient f y)) x :=
    hgrad.inner_bundle hgrad
  exact (((contDiffAt_inv ℝ hregular).contMDiffAt.comp x hpair).neg).smul_section hgrad

/-- The defining normalization gives unit decrease of the scalar function. -/
theorem mvfderiv_normalizedNegGradient (D : LeviCivitaData g)
    (f : M → ℝ) (x : M)
    (hregular : g.inner x (D.gradient f x) (D.gradient f x) ≠ 0) :
    mvfderiv (𝓡 n) f x (normalizedNegGradient D f x) = -1 := by
  simp only [normalizedNegGradient, map_smul, smul_eq_mul, ← D.inner_gradient]
  field_simp

/-- Differentiating a scalar multiple of the gradient in a level-tangent
direction eliminates the derivative of the scalar factor. -/
theorem inner_connection_smul_gradient_of_tangent
    (D : LeviCivitaData g) {f a : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (ha : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ) a x)
    (v : TangentSpace (𝓡 n) x) (hv : mvfderiv (𝓡 n) f x v = 0) :
    g.inner x (D.connection (fun y => a y • D.gradient f y) x v) v =
      a x * D.hessian f x v v := by
  have hgrad := (D.contMDiffAt_gradient hf).mdifferentiableAt (by simp)
  have hleib := D.connection.isCovariantDerivativeOn.leibniz hgrad ha
  have he := congrArg (fun A => g.inner x (A v) v) hleib
  simpa only [Pi.smul_def', Pi.smul_apply, add_apply,
    ContinuousLinearMap.smulRight_apply, map_add, map_smul, smul_apply,
    smul_eq_mul, D.inner_gradient, hv, mul_zero, add_zero, zero_add,
    D.hessian_eq_inner_connection_gradient hf] using he

/-- The exact tangential derivative identity for the normalized negative
gradient, including the cancellation of its normalization derivative. -/
theorem inner_connection_normalized_neg_gradient
    (D : LeviCivitaData g) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (hregular : g.inner x (D.gradient f x) (D.gradient f x) ≠ 0)
    (v : TangentSpace (𝓡 n) x) (hv : mvfderiv (𝓡 n) f x v = 0) :
    g.inner x (D.connection
      (fun y => -(g.inner y (D.gradient f y) (D.gradient f y))⁻¹ • D.gradient f y)
      x v) v =
      -(D.hessian f x v v / g.inner x (D.gradient f x) (D.gradient f x)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hgrad := (D.contMDiffAt_gradient hf).mdifferentiableAt (by simp)
  have hpair : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => g.inner y (D.gradient f y) (D.gradient f y)) x :=
    hgrad.inner_bundle hgrad
  have hinv : MDifferentiableAt (𝓡 n) 𝓘(ℝ, ℝ)
      (fun y => -(g.inner y (D.gradient f y) (D.gradient f y))⁻¹) x :=
    ((differentiableAt_inv hregular).mdifferentiableAt.comp x hpair).neg
  rw [inner_connection_smul_gradient_of_tangent D hf hinv v hv]
  ring

/-- A lower Hessian bound and an upper squared-gradient bound make the
normalized negative gradient strictly contracting in level-tangent directions. -/
theorem inner_connection_normalized_neg_gradient_le
    (D : LeviCivitaData g) {f : M → ℝ} {x : M}
    (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x)
    (hregular : 0 < g.inner x (D.gradient f x) (D.gradient f x))
    {η B : ℝ} (hη : 0 ≤ η)
    (hupper : g.inner x (D.gradient f x) (D.gradient f x) ≤ B)
    (v : TangentSpace (𝓡 n) x) (hv : mvfderiv (𝓡 n) f x v = 0)
    (hhess : η * g.inner x v v ≤ D.hessian f x v v) :
    g.inner x (D.connection
      (fun y => -(g.inner y (D.gradient f y) (D.gradient f y))⁻¹ • D.gradient f y)
      x v) v ≤ -(η / B) * g.inner x v v := by
  rw [inner_connection_normalized_neg_gradient D hf hregular.ne' v hv]
  have hvv : 0 ≤ g.inner x v v := by
    by_cases hz : v = 0
    · simp [hz]
    · exact (g.pos x v hz).le
  have h₁ := div_le_div_of_nonneg_left (mul_nonneg hη hvv) hregular hupper
  have h₂ := div_le_div_of_nonneg_right hhess hregular.le
  calc
    -(D.hessian f x v v / g.inner x (D.gradient f x) (D.gradient f x))
        ≤ -((η * g.inner x v v) / B) := neg_le_neg (h₁.trans h₂)
    _ = -(η / B) * g.inner x v v := by ring

/-- Integration of the squared-length differential inequality. Applied to
a variation field of a normalized gradient flow, this gives the metric
contraction factor in Eschenburg's Lemma 7.5. -/
theorem squared_length_le_exp_of_derivative_bound
    {q q' : ℝ → ℝ} {a b c : ℝ}
    (hq : ContinuousOn q (Icc a b))
    (hq' : ∀ t ∈ Ico a b, HasDerivAt q (q' t) t)
    (hbound : ∀ t ∈ Ico a b, q' t ≤ -2 * c * q t) :
    ∀ t ∈ Icc a b, q t ≤ q a * Real.exp (-2 * c * (t - a)) := by
  have h := le_gronwallBound_of_liminf_deriv_right_le
    (f := q) (f' := q') (δ := q a) (K := -2 * c) (ε := 0) hq
    (fun t ht r hr => (hq' t ht).hasDerivWithinAt.liminf_right_slope_le hr)
    le_rfl (by simpa only [add_zero] using hbound)
  simpa only [gronwallBound_ε0] using h

end Poincare.Geometry.Riemannian.Convexity
