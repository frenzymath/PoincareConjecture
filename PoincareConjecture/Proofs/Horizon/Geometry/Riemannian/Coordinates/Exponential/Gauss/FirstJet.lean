import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.GaussMetricExtension

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.CoordinateExponential

theorem metric_zero_eq_innerSL_of_gauss
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {B : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hB : DifferentiableAt ℝ B 0)
    (hgauss : ∀ᶠ x in 𝓝 0, ∀ w, B x x w = inner ℝ x w) :
    B 0 = innerSL ℝ := by
  ext v w
  change B 0 v w = inner ℝ v w
  have hd := ((hB.hasFDerivAt.clm_apply (hasFDerivAt_id 0)).clm_apply
    (hasFDerivAt_const w 0)).fderiv
  have heq : (fun x => B x x w) =ᶠ[𝓝 0] (innerSL ℝ).flip w :=
    hgauss.mono fun x hx => hx w
  simp only [id_eq] at hd
  rw [heq.fderiv_eq, ContinuousLinearMap.fderiv] at hd
  have hh := congrArg (fun L => L v) hd
  simpa only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_zero, zero_add,
    innerSL_apply_apply, map_zero, zero_apply, add_zero] using hh.symm

theorem christoffelBilinear_zero_of_local_gauss
    {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ U)
    (B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B U)
    (hsymm : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (hpos : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < B x v v)
    (hgauss : ∀ x ∈ U, ∀ w, B x x w = inner ℝ x w) :
    christoffelBilinear B 0 = 0 := by
  let E := EuclideanSpace ℝ (Fin n)
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hzero)
  obtain ⟨g, _D, heq, hG⟩ := exists_gauss_metric_extension
    (by linarith : 0 < R / 4) (by linarith : R / 4 < R / 2)
    (by linarith : R / 2 < R) B (hB.mono hRU)
    (fun x hx => hsymm x (hRU hx)) (fun x hx => hpos x (hRU hx))
    (fun x hx => hgauss x (hRU hx))
  have hgerm : g.euclideanCoefficients =ᶠ[𝓝 (0 : E)] B := by
    filter_upwards [Metric.ball_mem_nhds (0 : E) (by linarith : 0 < R / 4)] with x hx
    exact heq x (Metric.ball_subset_closedBall hx)
  have hΓ : christoffelBilinear B 0 = christoffelBilinear g.euclideanCoefficients 0 := by
    unfold christoffelBilinear
    rw [hgerm.self_of_nhds, hgerm.fderiv_eq]
  rw [hΓ]
  have hgs : ContDiff ℝ ∞ g.euclideanCoefficients :=
    contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients
  have hdiag (v : E) : christoffelBilinear g.euclideanCoefficients 0 v v = 0 := by
    simpa only [zero_smul] using christoffelBilinear_radial_eq_zero_of_gauss
      hgs g.inner_isInvertible g.symm hG v 0
  have hsym (v w : E) : christoffelBilinear g.euclideanCoefficients 0 v w =
      christoffelBilinear g.euclideanCoefficients 0 w v :=
    christoffelBilinear_symm (hgs.differentiable (by simp) 0)
      (Eventually.of_forall g.symm) v w
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  have hpolar := hdiag (v + w)
  simp only [map_add, add_apply, hdiag v, hdiag w, zero_add, add_zero,
    ← hsym v w] at hpolar
  have htwice : (2 : ℝ) • christoffelBilinear g.euclideanCoefficients 0 v w = 0 := by
    simpa only [two_smul] using hpolar
  simpa only [smul_eq_zero, OfNat.ofNat_ne_zero, false_or, zero_apply] using htwice

end PoincareConjecture.CoordinateExponential
