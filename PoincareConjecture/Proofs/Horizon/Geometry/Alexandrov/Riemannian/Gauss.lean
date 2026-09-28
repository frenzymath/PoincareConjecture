import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.RadialHessian

noncomputable section
set_option autoImplicit false

open Filter
open scoped Topology

namespace PoincareConjecture.CoordinateExponential.Alexandrov

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem radial_christoffel_identities
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hB : DifferentiableAt ℝ B x) (hinv : (B x).IsInvertible)
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ a b, B y a b = B y b a)
    (hgauss : ∀ᶠ y in 𝓝 x, ∀ w, B y y w = inner ℝ y w) :
    coordinateChristoffel B x x x = 0 ∧
      ∀ w, B x (coordinateChristoffel B x x w) x = 0 := by
  have hd (d w : E) : fderiv ℝ B x d x w + B x d w = inner ℝ d w := by
    have hl := (hB.hasFDerivAt.clm_apply (hasFDerivAt_id x)).clm_apply
      (hasFDerivAt_const w x)
    have hr := (hasFDerivAt_id x).inner ℝ (hasFDerivAt_const w x)
    have heq : (fun y => B y y w) =ᶠ[𝓝 x] (fun y => inner ℝ y w) :=
      hgauss.mono fun y hy => hy w
    have h := congrArg (fun L : E →L[ℝ] ℝ => L d)
      (hl.fderiv.symm.trans (heq.fderiv_eq.trans hr.fderiv))
    simpa only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply,
      zero_apply, map_zero, zero_add, add_zero, id_eq, fderivInnerCLM_apply,
      ContinuousLinearMap.prod_apply, inner_zero_right, add_comm] using h
  have h1 (w : E) : fderiv ℝ B x x x w = 0 := by
    have h := hd x w
    rw [hgauss.self_of_nhds w] at h
    linarith
  have h2 (w : E) : fderiv ℝ B x w x x = 0 := by
    have h := hd w x
    rw [hsymm.self_of_nhds w x, hgauss.self_of_nhds w, real_inner_comm x w] at h
    linarith
  have hds (d v w : E) : fderiv ℝ B x d v w = fderiv ℝ B x d w v := by
    have happ (v w : E) : fderiv ℝ (fun y => B y v w) x d =
        fderiv ℝ B x d v w := by
      have h := ((hB.hasFDerivAt.clm_apply (hasFDerivAt_const v x)).clm_apply
        (hasFDerivAt_const w x)).fderiv
      simpa only [ContinuousLinearMap.comp_zero, zero_add,
        ContinuousLinearMap.flip_apply] using congrArg (fun L => L d) h
    rw [← happ v w, ← happ w v]
    have heq : (fun y => B y v w) =ᶠ[𝓝 x] (fun y => B y w v) :=
      hsymm.mono fun y hy => hy v w
    exact congrArg (fun L : E →L[ℝ] ℝ => L d) heq.fderiv_eq
  constructor
  · change (B x).inverse (metricKoszulCovector (fderiv ℝ B x) x x) = 0
    have hk : metricKoszulCovector (fderiv ℝ B x) x x = 0 := by
      ext w
      simp only [metricKoszulCovector, smul_apply, add_apply, sub_apply,
        ContinuousLinearMap.flip_apply, smul_eq_mul, zero_apply]
      rw [hds x w x, h1, h2]
      ring
    rw [hk, map_zero]
  · intro w
    have hm := fderiv_metric_eq_christoffel hB hinv hsymm x x w
    have hs := christoffelBilinear_symm hB hsymm w x
    simp only [christoffelBilinear_apply] at hs
    rw [h2, hs, hsymm.self_of_nhds x (coordinateChristoffel B x x w)] at hm
    linarith

theorem radial_quadratic_refinement
    (B : E →L[ℝ] E →L[ℝ] ℝ) (G : E →L[ℝ] E) {x : E} {k : ℝ}
    (hx : x ≠ 0) (hB : ∀ v w, B v w = B w v)
    (hgauss : ∀ w, B x w = inner ℝ x w)
    (hGx : G x = 0) (hGorth : ∀ w, B (G w) x = 0)
    (hbound : ∀ w, B (w + G w) w ≤ k * B w w) (w : E) :
    B (w + G w) w ≤ k * B w w +
      (1 - k) * (inner ℝ x w) ^ 2 / ‖x‖ ^ 2 := by
  let α : ℝ := inner ℝ x w / ‖x‖ ^ 2
  have hnorm : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hdiag : B x x = ‖x‖ ^ 2 := by rw [hgauss, real_inner_self_eq_norm_sq]
  have hcross : B w x = inner ℝ x w := by rw [hB, hgauss]
  have hG : G (w - α • x) = G w := by simp [map_sub, hGx]
  have h := hbound (w - α • x)
  rw [hG] at h
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul, map_add, add_apply,
    hdiag, hcross, hgauss, hGorth] at h
  have hα : α * ‖x‖ ^ 2 = inner ℝ x w := div_mul_cancel₀ _ hnorm
  have hαinner : α * inner ℝ x w = (inner ℝ x w) ^ 2 / ‖x‖ ^ 2 := by
    dsimp [α]
    ring
  simp only [hα, sub_self, zero_add, mul_zero, sub_zero] at h
  rw [hαinner, mul_sub] at h
  simp only [map_add, add_apply]
  rw [mul_div_assoc, sub_mul, one_mul]
  linarith only [h]

end PoincareConjecture.CoordinateExponential.Alexandrov
