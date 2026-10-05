import PoincareLib.Geometry.Riemannian.Tensor.MaximumPrinciple.Transport.Radial
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Metric preservation by radial parallel transport

Differentiate the varying bilinear form on two solutions of the radial
parallel equation. Compatibility cancels the derivative of the form against
both vector derivatives. The resulting endpoint identity holds when the
metric is defined and compatible only on a neighborhood of the radial
segment. Symmetry and positivity are not needed for this bilinear identity.

Source: Morgan--Tian, Claim 4.2, printed p. 64, using metric-compatible
parallel transport in the local supporting-functional construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped ContDiff

namespace Poincare.Riemannian.RadialTransport

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
lemma metric_fderiv_apply {G : E → F →L[ℝ] F →L[ℝ] ℝ} {x : E}
    (hG : DifferentiableAt ℝ G x) (u : E) (a b : F) :
    fderiv ℝ (fun z => G z a b) x u = fderiv ℝ G x u a b := by
  have h := (hG.hasFDerivAt.clm_apply (hasFDerivAt_const a x)).clm_apply
    (hasFDerivAt_const b x)
  have hh := congrArg (fun L => L u) h.fderiv
  simpa using hh

omit [CompleteSpace F] in
/-- Compatibility cancels the full metric derivative on two arbitrary curves
satisfying the radial parallel equations. -/
lemma metric_pairing_hasDerivAt_zero
    {Γ : E → E →L[ℝ] F →L[ℝ] F}
    {G : E → F →L[ℝ] F →L[ℝ] ℝ} (x : E) {V W : ℝ → F} {t : ℝ}
    (hG : DifferentiableAt ℝ G (t • x))
    (hcompat : ∀ a b : F, fderiv ℝ (fun z => G z a b) (t • x) x =
      G (t • x) (Γ (t • x) x a) b + G (t • x) a (Γ (t • x) x b))
    (hV : HasDerivAt V (-(Γ (t • x) x (V t))) t)
    (hW : HasDerivAt W (-(Γ (t • x) x (W t))) t) :
    HasDerivAt (fun r => G (r • x) (V r) (W r)) 0 t := by
  have hcurve : HasDerivAt (fun r : ℝ => G (r • x))
      (fderiv ℝ G (t • x) x) t := by
    have hray : HasDerivAt (fun r : ℝ => r • x) x t := by
      simpa only [id_eq, one_smul] using (hasDerivAt_id t).smul_const x
    exact HasFDerivAt.comp_hasDerivAt (l := G) (f := fun r : ℝ => r • x)
      t hG.hasFDerivAt hray
  have h := (hcurve.clm_apply hV).clm_apply hW
  have hc (a b : F) : fderiv ℝ G (t • x) x a b =
      G (t • x) (Γ (t • x) x a) b + G (t • x) a (Γ (t • x) x b) := by
    rw [← metric_fderiv_apply hG]
    exact hcompat a b
  convert h using 1 <;> first | rfl | (simp only [add_apply, map_neg, neg_apply, hc]; ring)

omit [CompleteSpace F] in
/-- Any two radial parallel curves preserve their metric pairing on the closed
segment. Only the actual local coefficient in their ODE is used. -/
theorem metric_pairing_eq_on_segment
    {Γ : E → E →L[ℝ] F →L[ℝ] F}
    {G : E → F →L[ℝ] F →L[ℝ] ℝ} {U : Set E} (hU : IsOpen U)
    (hG : DifferentiableOn ℝ G U)
    (hcompat : ∀ z ∈ U, ∀ u : E, ∀ a b : F, fderiv ℝ (fun y => G y a b) z u =
      G z (Γ z u a) b + G z a (Γ z u b))
    (x : E) (hx : ∀ t ∈ Icc (0 : ℝ) 1, t • x ∈ U) (V W : ℝ → F)
    (hV : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt V (-(Γ (t • x) x (V t))) t)
    (hW : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt W (-(Γ (t • x) x (W t))) t)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    G (t • x) (V t) (W t) = G 0 (V 0) (W 0) := by
  let f : ℝ → ℝ := fun r => G (r • x) (V r) (W r)
  have hd (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) : HasDerivAt f 0 r :=
    metric_pairing_hasDerivAt_zero x
      ((hG _ (hx r hr)).differentiableAt (hU.mem_nhds (hx r hr)))
      (hcompat _ (hx r hr) x) (hV r hr) (hW r hr)
  have hbound := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := fun _ => (0 : ℝ)) (C := 0)
    (fun r hr => (hd r hr).hasDerivWithinAt) (fun _ _ => by simp)
    (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) ht
  have heq : f t = f 0 := sub_eq_zero.mp (norm_le_zero_iff.mp (by simpa using hbound))
  simpa only [f, zero_smul] using heq

omit [CompleteSpace F] in
/-- The endpoint version for arbitrary coordinate fields parallel along the
radial segment. Their construction may use different cutoff coefficients. -/
theorem fields_metric_eq_of_radial_parallel
    {Γ : E → E →L[ℝ] F →L[ℝ] F}
    {G : E → F →L[ℝ] F →L[ℝ] ℝ} {U : Set E} (hU : IsOpen U)
    (hG : DifferentiableOn ℝ G U)
    (hcompat : ∀ z ∈ U, ∀ u : E, ∀ a b : F, fderiv ℝ (fun y => G y a b) z u =
      G z (Γ z u a) b + G z a (Γ z u b))
    (x : E) (hx : ∀ t ∈ Icc (0 : ℝ) 1, t • x ∈ U) (Y Z : E → F)
    (hY : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun r : ℝ => Y (r • x)) (-(Γ (t • x) x (Y (t • x)))) t)
    (hZ : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun r : ℝ => Z (r • x)) (-(Γ (t • x) x (Z (t • x)))) t) :
    G x (Y x) (Z x) = G 0 (Y 0) (Z 0) := by
  simpa only [one_smul, zero_smul] using
    metric_pairing_eq_on_segment hU hG hcompat x hx
      (fun r => Y (r • x)) (fun r => Z (r • x)) hY hZ (t := 1) (by norm_num)

/-- The actual radial ODE solutions have zero derivative of their metric pairing. -/
lemma solution_metric_hasDerivAt_zero
    {Γ : E → E →L[ℝ] F →L[ℝ] F} (hΓ : ContDiff ℝ ∞ Γ)
    {G : E → F →L[ℝ] F →L[ℝ] ℝ} (x : E) (v w : F)
    {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2)
    (hG : DifferentiableAt ℝ G (t • x))
    (hcompat : ∀ a b : F, fderiv ℝ (fun z => G z a b) (t • x) x =
      G (t • x) (Γ (t • x) x a) b + G (t • x) a (Γ (t • x) x b)) :
    HasDerivAt (fun r => G (r • x) (solution Γ v x r) (solution Γ w x r)) 0 t :=
  metric_pairing_hasDerivAt_zero x hG hcompat
    (solution_hasDerivAt hΓ v x ht) (solution_hasDerivAt hΓ w x ht)

/-- The varying metric pairing is constant along the constructed radial solution. -/
theorem solution_metric_eq_on_segment
    {Γ : E → E →L[ℝ] F →L[ℝ] F} (hΓ : ContDiff ℝ ∞ Γ)
    {G : E → F →L[ℝ] F →L[ℝ] ℝ} {U : Set E} (hU : IsOpen U)
    (hG : DifferentiableOn ℝ G U)
    (hcompat : ∀ z ∈ U, ∀ u : E, ∀ a b : F, fderiv ℝ (fun y => G y a b) z u =
      G z (Γ z u a) b + G z a (Γ z u b))
    (x : E) (hx : ∀ t ∈ Icc (0 : ℝ) 1, t • x ∈ U) (v w : F)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    G (t • x) (solution Γ v x t) (solution Γ w x t) = G 0 v w := by
  have htime {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) : r ∈ Ioo (-2 : ℝ) 2 :=
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  simpa only [solution_zero] using
    metric_pairing_eq_on_segment hU hG hcompat x hx (solution Γ v x) (solution Γ w x)
      (fun _ hr => solution_hasDerivAt hΓ v x (htime hr))
      (fun _ hr => solution_hasDerivAt hΓ w x (htime hr)) ht

/-- Radial transport preserves the metric from the center to the endpoint. -/
theorem field_metric_eq
    {Γ : E → E →L[ℝ] F →L[ℝ] F} (hΓ : ContDiff ℝ ∞ Γ)
    {G : E → F →L[ℝ] F →L[ℝ] ℝ} {U : Set E} (hU : IsOpen U)
    (hG : DifferentiableOn ℝ G U)
    (hcompat : ∀ z ∈ U, ∀ u : E, ∀ a b : F, fderiv ℝ (fun y => G y a b) z u =
      G z (Γ z u a) b + G z a (Γ z u b))
    (x : E) (hx : ∀ t ∈ Icc (0 : ℝ) 1, t • x ∈ U) (v w : F) :
    G x (field Γ v x) (field Γ w x) = G 0 v w := by
  simpa only [one_smul, field] using
    solution_metric_eq_on_segment hΓ hU hG hcompat x hx v w (t := 1) (by norm_num)

end Poincare.Riemannian.RadialTransport
