import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.RadialGauss
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.AlongCurve.Metric










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.CoordinateExponential

open ConnectionVariation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem deriv2_norm_sq
    {u : ℝ → E} {t : ℝ} (hu : ContDiffAt ℝ 1 u t)
    (hu' : DifferentiableAt ℝ (deriv u) t) :
    (deriv^[2] (fun s => ‖u s‖ ^ 2)) t =
      2 * (inner ℝ (deriv u t) (deriv u t) + inner ℝ (u t) (deriv (deriv u) t)) := by
  have hfirst : deriv (fun s => ‖u s‖ ^ 2) =ᶠ[𝓝 t]
      (fun s => 2 * inner ℝ (u s) (deriv u s)) := by
    filter_upwards [hu.eventually (by simp)] with s hs
    exact ((hs.differentiableAt (by norm_num)).hasDerivAt.norm_sq).deriv
  have hsecond := ((hu.differentiableAt (by norm_num)).hasDerivAt.inner ℝ
    hu'.hasDerivAt).const_mul 2
  change deriv (deriv (fun s => ‖u s‖ ^ 2)) t = _
  rw [hfirst.deriv_eq, hsecond.deriv]
  ring



theorem radial_hessian_pairing_of_gauss
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hB : DifferentiableAt ℝ B x) (hinv : (B x).IsInvertible)
    (hsymm : ∀ᶠ y in 𝓝 x, ∀ a b, B y a b = B y b a)
    (hgauss : ∀ᶠ y in 𝓝 x, ∀ w, B y y w = inner ℝ y w) (w : E) :
    inner ℝ w w - inner ℝ x (coordinateChristoffel B x w w) =
      B x (w + coordinateChristoffel B x x w) w := by
  have hleft := (hB.hasFDerivAt.clm_apply (hasFDerivAt_id x)).clm_apply
    (hasFDerivAt_const w x)
  have hright := (hasFDerivAt_id x).inner ℝ (hasFDerivAt_const w x)
  have heq : (fun y => B y y w) =ᶠ[𝓝 x] (fun y => inner ℝ y w) :=
    hgauss.mono fun y hy => hy w
  have hd := congrArg (fun L : E →L[ℝ] ℝ => L w)
    (hleft.fderiv.symm.trans (heq.fderiv_eq.trans hright.fderiv))
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.id_apply,
    zero_apply, map_zero, zero_add, id_eq, fderivInnerCLM_apply,
    ContinuousLinearMap.prod_apply, inner_zero_right] at hd
  have hm := fderiv_metric_eq_christoffel hB hinv hsymm x w w
  have hs := christoffelBilinear_symm hB hsymm w x
  simp only [christoffelBilinear_apply] at hs
  rw [hs, hgauss.self_of_nhds (coordinateChristoffel B x w w)] at hm
  simp only [map_add, add_apply]
  linarith



theorem deriv2_norm_sq_eq_radial_pairing
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {u : ℝ → E} {t : ℝ}
    (hB : DifferentiableAt ℝ B (u t)) (hinv : (B (u t)).IsInvertible)
    (hsymm : ∀ᶠ y in 𝓝 (u t), ∀ a b, B y a b = B y b a)
    (hgauss : ∀ᶠ y in 𝓝 (u t), ∀ w, B y y w = inner ℝ y w)
    (hu : ContDiffAt ℝ 1 u t)
    (hu' : DifferentiableAt ℝ (deriv u) t)
    (hgeo : deriv (deriv u) t =
      -coordinateChristoffel B (u t) (deriv u t) (deriv u t)) :
    (deriv^[2] (fun s => ‖u s‖ ^ 2)) t =
      2 * B (u t) (deriv u t +
        coordinateChristoffel B (u t) (u t) (deriv u t)) (deriv u t) := by
  rw [deriv2_norm_sq hu hu', hgeo, inner_neg_right]
  have hp := radial_hessian_pairing_of_gauss hB hinv hsymm hgauss (deriv u t)
  linarith



theorem radial_covDerivAt_one
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (x w : E) :
    covDerivAlong (christoffelBilinear B)
      (fun r : ℝ => r • x) (fun r : ℝ => r • w) 1 1 =
        w + coordinateChristoffel B x x w := by
  have hline (v : E) : HasDerivAt (fun r : ℝ => r • v) v 1 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (1 : ℝ)).smul_const v
  simp only [covDerivAlong, fderiv_eq_smul_deriv, one_smul,
    (hline w).deriv, (hline x).deriv, christoffelBilinear_apply]



theorem deriv2_norm_sq_eq_radial_covDeriv_pairing
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {u : ℝ → E} {t : ℝ}
    (hB : DifferentiableAt ℝ B (u t)) (hinv : (B (u t)).IsInvertible)
    (hsymm : ∀ᶠ y in 𝓝 (u t), ∀ a b, B y a b = B y b a)
    (hgauss : ∀ᶠ y in 𝓝 (u t), ∀ w, B y y w = inner ℝ y w)
    (hu : ContDiffAt ℝ 2 u t)
    (hgeo : deriv (deriv u) t =
      -coordinateChristoffel B (u t) (deriv u t) (deriv u t)) :
    (deriv^[2] (fun s => ‖u s‖ ^ 2)) t =
      2 * B (u t)
        (covDerivAlong (christoffelBilinear B)
          (fun r : ℝ => r • u t) (fun r : ℝ => r • deriv u t) 1 1)
        (deriv u t) := by
  rw [radial_covDerivAt_one]
  have hu' : DifferentiableAt ℝ (deriv u) t := by
    simpa only [fderiv_eq_smul_deriv, one_smul] using
      (((hu.fderiv_right (m := 1) (by norm_num)).clm_apply
        (contDiffAt_const (c := (1 : ℝ)))).differentiableAt (by norm_num))
  exact deriv2_norm_sq_eq_radial_pairing hB hinv hsymm hgauss
    (hu.of_le (by norm_num)) hu' hgeo

end PoincareConjecture.CoordinateExponential

namespace PoincareConjecture.RiemannianMetric

open CoordinateExponential



theorem IsGeodesicOn.deriv2_norm_sq_eq_radial_pairing
    {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {u : ℝ → EuclideanSpace ℝ (Fin n)} {I : Set ℝ}
    (hgeo : g.IsGeodesicOn u I) (hI : IsOpen I) {t : ℝ} (ht : t ∈ I)
    (hgauss : ∀ᶠ y in 𝓝 (u t), ∀ w, g.inner y y w = inner ℝ y w) :
    (deriv^[2] (fun s => ‖u s‖ ^ 2)) t =
      2 * g.inner (u t) (deriv u t +
        coordinateChristoffel g.euclideanCoefficients (u t) (u t) (deriv u t))
        (deriv u t) := by
  have hode := (hgeo.hasDerivAt_in_chart hI (u t)
    (by simp) t ht).2
  have hcoeff : g.pullbackCoefficients id = g.euclideanCoefficients := by
    ext x v w
    simp only [pullbackCoefficients, mfderiv_id, euclideanCoefficients]
    rfl
  have heq : deriv (deriv u) t =
      -coordinateChristoffel g.euclideanCoefficients (u t) (deriv u t) (deriv u t) := by
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
      PartialEquiv.refl_coe, hcoeff, id_eq] using hode.deriv
  have hu' : DifferentiableAt ℝ (deriv u) t := by
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq]
      using hode.differentiableAt
  exact CoordinateExponential.deriv2_norm_sq_eq_radial_pairing
    ((g.contDiffAt_euclideanCoefficients (u t)).differentiableAt (by simp))
    (g.inner_isInvertible (u t))
    (Filter.Eventually.of_forall fun y a b => g.symm _ _ _) hgauss
    (contMDiffAt_iff_contDiffAt.mp (hgeo.contMDiffAt ht)) hu' heq

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem deriv2_norm_sq_eq_precompact_radial_pairing
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {e : EuclideanSpace ℝ (Fin n) → M} {R : ℝ}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hnorm : ∀ a b, g.pullbackCoefficients e 0 a b = inner ℝ a b)
    (hradial : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun r : ℝ => e (r • v))
        {r : ℝ | r • v ∈ Metric.ball 0 R})
    {u : ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hut : u t ∈ Metric.ball 0 R)
    (hi : Function.Bijective (mfderiv (𝓡 n) (𝓡 n) e (u t)))
    (hu : ContDiffAt ℝ 2 u t)
    (hgeo : deriv (deriv u) t =
      -coordinateChristoffel (g.pullbackCoefficients e) (u t) (deriv u t) (deriv u t)) :
    (deriv^[2] (fun s => ‖u s‖ ^ 2)) t =
      2 * g.pullbackCoefficients e (u t) (deriv u t +
        coordinateChristoffel (g.pullbackCoefficients e) (u t) (u t) (deriv u t))
        (deriv u t) := by
  have hat := he.contMDiffAt (Metric.isOpen_ball.mem_nhds hut)
  have hu' : DifferentiableAt ℝ (deriv u) t := by
    simpa only [fderiv_eq_smul_deriv, one_smul] using
      (((hu.fderiv_right (m := 1) (by norm_num)).clm_apply
        (contDiffAt_const (c := (1 : ℝ)))).differentiableAt (by norm_num))
  apply deriv2_norm_sq_eq_radial_pairing
    ((g.contDiffAt_pullbackCoefficients hat).differentiableAt (by simp))
    (g.isInvertible_pullbackCoefficients hi.1) _ _ (hu.of_le (by norm_num)) hu' hgeo
  · exact Filter.Eventually.of_forall fun y a b => g.symm _ _ _
  · filter_upwards [Metric.isOpen_ball.mem_nhds hut] with y hy w
    exact g.radial_gauss_identity D he hnorm hradial y hy w

end PoincareConjecture.RiemannianMetric
