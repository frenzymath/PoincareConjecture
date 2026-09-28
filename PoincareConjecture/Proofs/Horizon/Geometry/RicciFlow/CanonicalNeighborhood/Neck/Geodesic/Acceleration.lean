import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Geodesic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients.ChristoffelEstimate
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients.InverseEstimate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Topology

namespace PoincareConjecture.CoordinateExponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma norm_coordinateChristoffel_le_of_ellipticity
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} {a G : ℝ}
    (ha : 0 < a)
    (hell : ∀ v : E, a * ‖v‖ ^ 2 ≤ (B x) v v)
    (hmetric : ‖fderiv ℝ B x‖ ≤ G) :
    ‖christoffelBilinear B x‖ ≤ (3 / (2 * a)) * G := by
  exact (norm_christoffelBilinear_le_of_ellipticity B x ha hell).trans
    (mul_le_mul_of_nonneg_left hmetric (by positivity))

theorem christoffel_difference_apply
    {B G : E → E →L[ℝ] E →L[ℝ] ℝ} {x u v : E} :
    christoffelBilinear B x u v - christoffelBilinear G x u v =
      (B x).inverse
          (metricKoszulCovector (fderiv ℝ B x) u v -
            metricKoszulCovector (fderiv ℝ G x) u v) +
        ((B x).inverse - (G x).inverse)
          (metricKoszulCovector (fderiv ℝ G x) u v) := by
  change (B x).inverse (metricKoszulCovector (fderiv ℝ B x) u v) -
      (G x).inverse (metricKoszulCovector (fderiv ℝ G x) u v) = _
  simp only [map_sub, sub_apply]
  abel

theorem norm_christoffel_difference_le
    {B G : E → E →L[ℝ] E →L[ℝ] ℝ} {x : E} {a DB DG H : ℝ}
    (ha : 0 < a)
    (hB : ∀ v : E, a * ‖v‖ ^ 2 ≤ (B x) v v)
    (hG : ∀ v : E, a * ‖v‖ ^ 2 ≤ (G x) v v)
    (hderiv : ‖fderiv ℝ B x - fderiv ℝ G x‖ ≤ DB)
    (hGderiv : ‖fderiv ℝ G x‖ ≤ DG)
    (hzero : ‖B x - G x‖ ≤ H) :
    ‖christoffelBilinear B x - christoffelBilinear G x‖ ≤
      (3 / (2 * a)) * DB + (H / a ^ 2) * ((3 / 2 : ℝ) * DG) := by
  have hDB : 0 ≤ DB := (norm_nonneg _).trans hderiv
  have hDG : 0 ≤ DG := (norm_nonneg _).trans hGderiv
  have hH : 0 ≤ H := (norm_nonneg _).trans hzero
  have hBinv : ‖(B x).inverse‖ ≤ 1 / a :=
    norm_inverse_le_of_ellipticity ha hB
  have hInv : ‖(B x).inverse - (G x).inverse‖ ≤ H / a ^ 2 := by
    exact (norm_inverse_sub_le_of_ellipticity ha hB hG).trans
      (div_le_div_of_nonneg_right hzero (sq_nonneg a))
  have hK (u v : E) :
      ‖metricKoszulCovector (fderiv ℝ B x) u v -
          metricKoszulCovector (fderiv ℝ G x) u v‖ ≤
        (3 / 2 : ℝ) * DB * ‖u‖ * ‖v‖ := by
    have hK' := norm_metricKoszulCovector_le
      (fderiv ℝ B x - fderiv ℝ G x) u v
    have heq : metricKoszulCovector (fderiv ℝ B x) u v -
        metricKoszulCovector (fderiv ℝ G x) u v =
        metricKoszulCovector (fderiv ℝ B x - fderiv ℝ G x) u v := by
      unfold metricKoszulCovector
      rw [← smul_sub]
      congr 1
      ext z
      simp only [add_apply, sub_apply, ContinuousLinearMap.flip_apply]
      ring
    rw [heq]
    exact hK'.trans (by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hderiv (by positivity)
        · exact norm_nonneg u
      · exact norm_nonneg v)
  have hKG (u v : E) :
      ‖metricKoszulCovector (fderiv ℝ G x) u v‖ ≤
        (3 / 2 : ℝ) * DG * ‖u‖ * ‖v‖ := by
    exact (norm_metricKoszulCovector_le (fderiv ℝ G x) u v).trans (by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hGderiv (by positivity)
        · exact norm_nonneg u
      · exact norm_nonneg v)
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro u v
  change ‖christoffelBilinear B x u v - christoffelBilinear G x u v‖ ≤ _
  rw [christoffel_difference_apply]
  have hfirst :
      ‖(B x).inverse
          (metricKoszulCovector (fderiv ℝ B x) u v -
            metricKoszulCovector (fderiv ℝ G x) u v)‖ ≤
        (1 / a) * ((3 / 2 : ℝ) * DB * ‖u‖ * ‖v‖) := by
    calc
      _ ≤ ‖(B x).inverse‖ *
          ‖metricKoszulCovector (fderiv ℝ B x) u v -
            metricKoszulCovector (fderiv ℝ G x) u v‖ :=
        (B x).inverse.le_opNorm _
      _ ≤ (1 / a) * ((3 / 2 : ℝ) * DB * ‖u‖ * ‖v‖) := by
        exact mul_le_mul hBinv (hK u v) (norm_nonneg _) (by positivity)
  have hsecond :
      ‖((B x).inverse - (G x).inverse)
          (metricKoszulCovector (fderiv ℝ G x) u v)‖ ≤
        (H / a ^ 2) * ((3 / 2 : ℝ) * DG * ‖u‖ * ‖v‖) := by
    calc
      _ ≤ ‖(B x).inverse - (G x).inverse‖ *
          ‖metricKoszulCovector (fderiv ℝ G x) u v‖ :=
        ((B x).inverse - (G x).inverse).le_opNorm _
      _ ≤ (H / a ^ 2) * ((3 / 2 : ℝ) * DG * ‖u‖ * ‖v‖) := by
        exact mul_le_mul hInv (hKG u v) (norm_nonneg _) (by positivity)
  calc
    ‖(B x).inverse
          (metricKoszulCovector (fderiv ℝ B x) u v -
            metricKoszulCovector (fderiv ℝ G x) u v) +
        ((B x).inverse - (G x).inverse)
          (metricKoszulCovector (fderiv ℝ G x) u v)‖ ≤
        ‖(B x).inverse
          (metricKoszulCovector (fderiv ℝ B x) u v -
            metricKoszulCovector (fderiv ℝ G x) u v)‖ +
        ‖((B x).inverse - (G x).inverse)
          (metricKoszulCovector (fderiv ℝ G x) u v)‖ := norm_add_le _ _
    _ ≤ (1 / a) * ((3 / 2 : ℝ) * DB * ‖u‖ * ‖v‖) +
        (H / a ^ 2) * ((3 / 2 : ℝ) * DG * ‖u‖ * ‖v‖) :=
      add_le_add hfirst hsecond
    _ = ((3 / (2 * a)) * DB + (H / a ^ 2) * ((3 / 2 : ℝ) * DG)) *
        ‖u‖ * ‖v‖ := by ring

lemma norm_geodesic_acceleration_le
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {q w : ℝ → E} {t : ℝ}
    {a G V : ℝ}
    (ha : 0 < a)
    (hell : ∀ v : E, a * ‖v‖ ^ 2 ≤ (B (q t)) v v)
    (hmetric : ‖fderiv ℝ B (q t)‖ ≤ G)
    (hvel : ‖w t‖ ≤ V)
    (hw : HasDerivAt w
      (-christoffelBilinear B (q t) (w t) (w t)) t) :
    ‖deriv w t‖ ≤ (3 / (2 * a)) * G * V ^ 2 := by
  rw [hw.deriv]
  have hΓ := norm_coordinateChristoffel_le_of_ellipticity ha hell hmetric
  have happ := (christoffelBilinear B (q t)).le_opNorm₂ (w t) (w t)
  have happ' : ‖christoffelBilinear B (q t) (w t) (w t)‖ ≤
      ((3 / (2 * a)) * G) * ‖w t‖ * ‖w t‖ := by
    exact happ.trans <| mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hΓ (norm_nonneg (w t))) (norm_nonneg (w t))
  rw [norm_neg]
  calc
    ‖christoffelBilinear B (q t) (w t) (w t)‖ ≤
        ((3 / (2 * a)) * G) * ‖w t‖ * ‖w t‖ := happ'
    _ ≤ ((3 / (2 * a)) * G) * V * V := by
      have hG0 : 0 ≤ G := (norm_nonneg _).trans hmetric
      have hG : 0 ≤ (3 / (2 * a)) * G := by positivity
      exact mul_le_mul (mul_le_mul_of_nonneg_left hvel hG) hvel
        (norm_nonneg (w t)) (mul_nonneg hG ((norm_nonneg (w t)).trans hvel))
    _ = (3 / (2 * a)) * G * V ^ 2 := by ring

theorem abs_coordinate_component_acceleration_le
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {q w : ℝ → E} {I : Set ℝ} {t : ℝ}
    {ell : E →L[ℝ] ℝ} {a G V : ℝ}
    (hI : IsOpen I) (ht : t ∈ I) (ha : 0 < a)
    (hell : ∀ s ∈ I, ∀ v : E, a * ‖v‖ ^ 2 ≤ (B (q s)) v v)
    (hmetric : ∀ s ∈ I, ‖fderiv ℝ B (q s)‖ ≤ G)
    (hvel : ∀ s ∈ I, ‖w s‖ ≤ V)
    (hq : ∀ s ∈ I, HasDerivAt q (w s) s)
    (hw : ∀ s ∈ I, HasDerivAt w
      (-christoffelBilinear B (q s) (w s) (w s)) s) :
    |deriv (deriv (ell ∘ q)) t| ≤
      ‖ell‖ * ((3 / (2 * a)) * G) * V ^ 2 := by
  have hfirst (s : ℝ) (hs : s ∈ I) :
      HasDerivAt (ell ∘ q) (ell (w s)) s := by
    simpa only [Function.comp_apply] using
      ell.hasFDerivAt.comp_hasDerivAt s (hq s hs)
  have hderiv : deriv (ell ∘ q) =ᶠ[𝓝 t] (fun s => ell (w s)) := by
    filter_upwards [hI.mem_nhds ht] with s hs
    exact (hfirst s hs).deriv
  have hsecond : HasDerivAt (deriv (ell ∘ q))
      (ell (-christoffelBilinear B (q t) (w t) (w t))) t := by
    have hraw := (hasDerivAt_const t ell).clm_apply (hw t ht)
    simpa only [zero_apply, zero_add] using hraw.congr_of_eventuallyEq hderiv
  rw [hsecond.deriv]
  calc
    |ell (-christoffelBilinear B (q t) (w t) (w t))| ≤
        ‖ell‖ * ‖christoffelBilinear B (q t) (w t) (w t)‖ := by
      simpa only [norm_neg, Real.norm_eq_abs] using
        ell.le_opNorm (-christoffelBilinear B (q t) (w t) (w t))
    _ ≤ ‖ell‖ * ((3 / (2 * a)) * G * V ^ 2) := by
      have hΓ := norm_coordinateChristoffel_le_of_ellipticity ha
        (hell t ht) (hmetric t ht)
      have happ := (christoffelBilinear B (q t)).le_opNorm₂ (w t) (w t)
      have happ' : ‖christoffelBilinear B (q t) (w t) (w t)‖ ≤
          ((3 / (2 * a)) * G) * ‖w t‖ * ‖w t‖ := by
        exact happ.trans <| mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hΓ (norm_nonneg (w t))) (norm_nonneg (w t))
      exact mul_le_mul_of_nonneg_left
        (happ'.trans (by
          have hG0 : 0 ≤ G := (norm_nonneg _).trans (hmetric t ht)
          have hG : 0 ≤ (3 / (2 * a)) * G := by positivity
          calc
            ((3 / (2 * a)) * G) * ‖w t‖ * ‖w t‖ ≤
                ((3 / (2 * a)) * G) * V * V := by
              exact mul_le_mul (mul_le_mul_of_nonneg_left (hvel t ht) hG)
                (hvel t ht) (norm_nonneg (w t))
                (mul_nonneg hG ((norm_nonneg (w t)).trans (hvel t ht)))
            _ = (3 / (2 * a)) * G * V ^ 2 := by ring))
        (norm_nonneg ell)
    _ = ‖ell‖ * ((3 / (2 * a)) * G) * V ^ 2 := by ring

end PoincareConjecture.CoordinateExponential
