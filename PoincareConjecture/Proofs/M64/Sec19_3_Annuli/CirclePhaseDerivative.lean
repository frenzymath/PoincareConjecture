import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusCircleCurrent
import PoincareConjecture.Proofs.M63.Mathlib.LocalDiffeomorphLift














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}





theorem m64CircleProduct_pairing_eq_lift_deriv
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {gamma : ℝ → P.charts.Point} {L : ℝ → ℝ} {x : ℝ}
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)) gamma x)
    (hL : DifferentiableAt ℝ L x)
    (hquot : ∀ y, P.circle.quotient (L y) = (gamma y).2) :
    (P.flow.metric t).inner (gamma x) (curveVelocity gamma x)
      (P.charts.circleUnit (gamma x)) = deriv L x := by
  let := P.charts.chartedSpace
  let := P.circle.chartedSpace
  have hsnd : MDifferentiable (𝓡 (n + 1)) (𝓡 1)
      (Prod.snd : P.charts.Point → P.circle.Point) :=
    (contMDiff_snd.comp P.charts.to_product_smooth).mdifferentiable (by simp)
  have hpr := mfderiv_comp_apply (f := gamma)
    (g := (Prod.snd : P.charts.Point → P.circle.Point)) x (hsnd (gamma x)) hgamma 1
  have hval : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) L x 1 = deriv L x := by
    rw [mfderiv_eq_fderiv, hL.hasDerivAt.hasFDerivAt.fderiv]
    exact ContinuousLinearMap.toSpanSingleton_apply_one ℝ _
  have hl := mfderiv_comp_apply (f := L) (g := P.circle.quotient) x
    (P.circle.quotient_smooth.mdifferentiableAt (by simp))
    hL.hasDerivAt.hasFDerivAt.hasMFDerivAt.mdifferentiableAt 1
  have heq : P.circle.quotient ∘ L = Prod.snd ∘ gamma := funext hquot
  rw [heq, hval] at hl
  have hv : (P.charts.split (gamma x) (curveVelocity gamma x)).2 =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 1) P.circle.quotient (L x) (deriv L x) := by
    rw [P.charts.split_circle]
    exact hpr.symm.trans hl
  rw [P.metric_eq]
  simp only [M62.CircleProductCharts.circleUnit, ContinuousLinearEquiv.apply_symm_apply,
    map_zero, zero_add]
  have hframe : P.circle.frame (P.circle.quotient (L x)) =
      mfderiv 𝓘(ℝ, ℝ) (𝓡 1) P.circle.quotient (L x) 1 := P.circle.frame_quotient (L x)
  rw [hv, ← hquot x, hframe]
  simpa +instances only [M62.CircleGeometry.quotient, M62.CircleGeometry.metricOnPoints,
    mul_one] using! P.circle.metric_quotient (L x) (deriv L x) 1

private theorem horizontal_smooth (x s : ℝ) :
    ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ (fun y => annulusPoint y s) x := by
  apply contMDiffAt_iff_contDiffAt.mpr
  apply (contDiffAt_piLp 2).mpr
  intro j
  fin_cases j
  · simpa [annulusPoint] using! (contDiffAt_id : ContDiffAt ℝ ∞ (id : ℝ → ℝ) x)
  · simpa [annulusPoint] using (contDiffAt_const (c := s) :
      ContDiffAt ℝ ∞ (fun _ : ℝ => s) x)






theorem m64Annulus_phase_contDiffAt
    (P : M62.CircleProductData F circumference)
    {f : LoopPlane → P.charts.Point} {L : ℝ → ℝ} {x s : ℝ}
    (hf : ContMDiffAt (𝓡 2) (𝓡 (n + 1)) ∞ f (annulusPoint x s))
    (hL : ContinuousAt L x)
    (hquot : ∀ y, P.circle.quotient (L y) = (f (annulusPoint y s)).2) :
    ContDiffAt ℝ ∞ L x := by
  let := P.charts.chartedSpace
  let := P.circle.chartedSpace
  have hgamma := hf.comp x (horizontal_smooth x s)
  have hproj := (contMDiff_snd.comp P.charts.to_product_smooth).contMDiffAt.comp x hgamma
  apply contMDiffAt_iff_contDiffAt.mp
  apply (P.circle.quotient_local_diffeomorph (L x)).contMDiffAt_of_comp
    (I := 𝓘(ℝ, ℝ)) le_rfl hL
  change ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ (P.circle.quotient ∘ L) x
  have heq : P.circle.quotient ∘ L = fun y => (f (annulusPoint y s)).2 := funext hquot
  rw [heq]
  exact hproj





theorem m64AnnulusCircleCurrent_eq_phase_deriv
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {f : LoopPlane → P.charts.Point} {L : ℝ → ℝ} {x s : ℝ}
    (hf : ContMDiffAt (𝓡 2) (𝓡 (n + 1)) ∞ f (annulusPoint x s))
    (hL : ContinuousAt L x)
    (hquot : ∀ y, P.circle.quotient (L y) = (f (annulusPoint y s)).2) :
    m64AnnulusCircleCurrent P t f 0 (annulusPoint x s) = deriv L x := by
  have h := m64CircleProduct_pairing_eq_lift_deriv P t
    ((hf.comp x (horizontal_smooth x s)).mdifferentiableAt (by simp))
    ((m64Annulus_phase_contDiffAt P hf hL hquot).differentiableAt (by simp)) hquot
  change (P.flow.metric t).inner (f (annulusPoint x s))
    (curveVelocity (fun y => f (annulusPoint y s)) x)
    (P.charts.circleUnit (f (annulusPoint x s))) = deriv L x at h
  rw [m64Annulus_horizontal_velocity (hf.mdifferentiableAt (by simp))] at h
  exact h

end PoincareConjecture
