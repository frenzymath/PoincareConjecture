import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Euclidean
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Gradient
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Hessian.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients.ChristoffelEstimate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

lemma hessian_eq_fderiv_sub_christoffel (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ ∞ f x) (v w : EuclideanSpace ℝ (Fin n)) :
    D.hessian f x v w = fderiv ℝ (fderiv ℝ f) x v w -
      fderiv ℝ f x (CoordinateExponential.christoffelBilinear g.euclideanCoefficients x v w) := by
  have hfm : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f x :=
    contMDiffAt_iff_contDiffAt.mpr hf
  have hw : MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
      (fun y : EuclideanSpace ℝ (Fin n) ↦ Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n)) y (E := TangentSpace (𝓡 n)) w) x := by
    apply ContMDiffAt.mdifferentiableAt (n := ∞) _ (by simp)
    rw [Bundle.contMDiffAt_totalSpace]
    exact ⟨contMDiffAt_id, by simpa using (contMDiffAt_const
      (I := 𝓡 n) (I' := 𝓡 n) (c := w) (x := x) (n := ∞))⟩
  have h := D.hessianOnFields_eq_inner_connection_gradient hfm
    (fun _ ↦ v) hw
  rw [← D.hessian_eq_inner_connection_gradient hfm v w] at h
  rw [← h, hessianOnFields, D.connection_const_eq_inverse]
  have hd := ((hf.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have heval := hd.clm_apply (hasFDerivAt_const w x)
  simp +instances only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
  change fderiv ℝ (fun y ↦ fderiv ℝ f y w) x v - _ = _
  rw [heval.fderiv]
  simp only [add_apply, ContinuousLinearMap.comp_apply, zero_apply, map_zero, zero_add]
  rfl

lemma abs_hessian_le_of_coordinate_bounds (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ ∞ f x) {B₁ B₂ G : ℝ}
    (hfirst : ‖fderiv ℝ f x‖ ≤ B₁)
    (hsecond : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ B₂)
    (hconn : ‖CoordinateExponential.christoffelBilinear g.euclideanCoefficients x‖ ≤ G)
    (v w : EuclideanSpace ℝ (Fin n)) :
    |D.hessian f x v w| ≤ (B₂ + B₁ * G) * ‖v‖ * ‖w‖ := by
  have hB₁ : 0 ≤ B₁ := (norm_nonneg _).trans hfirst
  rw [D.hessian_eq_fderiv_sub_christoffel hf v w]
  have hsecond' : |fderiv ℝ (fderiv ℝ f) x v w| ≤ B₂ * ‖v‖ * ‖w‖ := by
    exact (fderiv ℝ (fderiv ℝ f) x).le_opNorm₂ v w |>.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsecond (norm_nonneg v))
        (norm_nonneg w))
  have hconn' : ‖CoordinateExponential.christoffelBilinear g.euclideanCoefficients x v w‖ ≤
      G * ‖v‖ * ‖w‖ :=
    (CoordinateExponential.christoffelBilinear g.euclideanCoefficients x).le_opNorm₂ v w |>.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconn (norm_nonneg v))
        (norm_nonneg w))
  have hfirst' : |fderiv ℝ f x
      (CoordinateExponential.christoffelBilinear g.euclideanCoefficients x v w)| ≤
      B₁ * (G * ‖v‖ * ‖w‖) :=
    (fderiv ℝ f x).le_opNorm _ |>.trans (mul_le_mul hfirst hconn' (norm_nonneg _) hB₁)
  calc
    _ ≤ |fderiv ℝ (fderiv ℝ f) x v w| +
        |fderiv ℝ f x (CoordinateExponential.christoffelBilinear g.euclideanCoefficients x v w)| :=
      abs_sub _ _
    _ ≤ B₂ * ‖v‖ * ‖w‖ + B₁ * (G * ‖v‖ * ‖w‖) := add_le_add hsecond' hfirst'
    _ = _ := by ring

lemma abs_hessian_le_of_elliptic_coordinate_bounds (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContDiffAt ℝ ∞ f x) {a B₁ B₂ G : ℝ} (ha : 0 < a)
    (hell : ∀ v : EuclideanSpace ℝ (Fin n), a * ‖v‖ ^ 2 ≤ g.inner x v v)
    (hfirst : ‖fderiv ℝ f x‖ ≤ B₁)
    (hsecond : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ B₂)
    (hmetric : ‖fderiv ℝ g.euclideanCoefficients x‖ ≤ G)
    (v w : EuclideanSpace ℝ (Fin n)) :
    |D.hessian f x v w| ≤ ((B₂ + B₁ * ((3 / (2 * a)) * G)) / a) *
      g.tangentNorm x v * g.tangentNorm x w := by
  have hconn := (CoordinateExponential.norm_christoffelBilinear_le_of_ellipticity
    g.euclideanCoefficients x ha hell).trans
      (mul_le_mul_of_nonneg_left hmetric (by positivity))
  have hcoord := D.abs_hessian_le_of_coordinate_bounds hf hfirst hsecond hconn v w
  have hB₁ : 0 ≤ B₁ := (norm_nonneg _).trans hfirst
  have hB₂ : 0 ≤ B₂ := (norm_nonneg _).trans hsecond
  have hG : 0 ≤ G := (norm_nonneg _).trans hmetric
  have hsqrt : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hnorm (z : EuclideanSpace ℝ (Fin n)) :
      ‖z‖ ≤ g.tangentNorm x z / Real.sqrt a := by
    apply (le_div_iff₀ hsqrt).mpr
    have h := Real.sqrt_le_sqrt (hell z)
    simpa only [Real.sqrt_mul ha.le, Real.sqrt_sq (norm_nonneg z),
      RiemannianMetric.tangentNorm, mul_comm] using h
  calc
    _ ≤ (B₂ + B₁ * ((3 / (2 * a)) * G)) * ‖v‖ * ‖w‖ := hcoord
    _ ≤ (B₂ + B₁ * ((3 / (2 * a)) * G)) *
        (g.tangentNorm x v / Real.sqrt a) *
        (g.tangentNorm x w / Real.sqrt a) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hnorm v) (by positivity)
      · exact hnorm w
      · exact norm_nonneg w
      · exact mul_nonneg (by positivity) (div_nonneg (Real.sqrt_nonneg _) hsqrt.le)
    _ = _ := by
      field_simp
      rw [Real.sq_sqrt ha.le]
      ring

lemma abs_hessian_le_of_elliptic_coordinate_lift (D : LeviCivitaData g)
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {h : RiemannianMetric n M} (D' : LeviCivitaData h)
    {e : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    {φ : M → ℝ} (c : ℝ)
    (he : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e x)
    (hinv : ∀ᶠ y in 𝓝 x, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible)
    (hpull : ∀ᶠ y in 𝓝 x, ∀ v w : TangentSpace (𝓡 n) y,
      g.inner y v w = h.inner (e y)
        (mfderiv (𝓡 n) (𝓡 n) e y v) (mfderiv (𝓡 n) (𝓡 n) e y w))
    (hφ : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ (e x))
    {a B₁ B₂ G : ℝ} (ha : 0 < a)
    (hell : ∀ v : EuclideanSpace ℝ (Fin n), a * ‖v‖ ^ 2 ≤ g.inner x v v)
    (hfirst : ‖fderiv ℝ (fun y ↦ φ (e y) - c) x‖ ≤ B₁)
    (hsecond : ‖fderiv ℝ (fderiv ℝ (fun y ↦ φ (e y) - c)) x‖ ≤ B₂)
    (hmetric : ‖fderiv ℝ g.euclideanCoefficients x‖ ≤ G)
    (v w : TangentSpace (𝓡 n) (e x)) :
    |D'.hessian φ (e x) v w| ≤ ((B₂ + B₁ * ((3 / (2 * a)) * G)) / a) *
      h.tangentNorm (e x) v * h.tangentNorm (e x) w := by
  simp_rw [fderiv_sub_const] at hfirst hsecond
  have hshift : fderiv ℝ (fun y ↦ φ (e y) - c) = fderiv ℝ (φ ∘ e) := by
    funext y
    exact fderiv_sub_const c
  rw [hshift] at hsecond
  apply D.abs_hessian_le_of_metric_pullback D' he hinv hpull hφ ?_ v w
  intro v' w'
  exact D.abs_hessian_le_of_elliptic_coordinate_bounds
    (contMDiffAt_iff_contDiffAt.mp (hφ.comp x he)) ha hell hfirst hsecond hmetric v' w'

end PoincareConjecture.LeviCivitaData
