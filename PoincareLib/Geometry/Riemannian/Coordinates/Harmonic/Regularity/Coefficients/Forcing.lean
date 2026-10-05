import PoincareLib.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Coefficients.Divergence
import PoincareLib.Geometry.Riemannian.ScalarOperators.Product

/-!
# Bounds for density-weighted scalar forcing

The Euclidean divergence expression controls the retained Laplacian by the
first derivative of the density-weighted inverse metric and the first two
ordinary derivatives of the scalar function. Its product rule gives cutoff
forcing bounds without introducing second derivatives of the other factor.
-/

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 12
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.HarmonicCoordinates

variable {n : ℕ}

/-- Euclidean duality preserves the norm of the scalar differential. -/
theorem norm_euclidean_gradient_eq (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖_root_.gradient f x‖ = ‖fderiv ℝ f x‖ := by
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.norm_map _

/-- Differentiating Euclidean duality does not increase the operator norm. -/
theorem norm_fderiv_euclidean_gradient_le {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ (_root_.gradient f) x‖ ≤ ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  let J := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  have heq : fderiv ℝ (_root_.gradient f) x =
      J.toContinuousLinearEquiv.toContinuousLinearMap.comp (fderiv ℝ (fderiv ℝ f) x) :=
    (J.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp x
      (hdf.differentiable (by simp) x).hasFDerivAt).fderiv
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  rw [heq, ContinuousLinearMap.comp_apply]
  change ‖J (fderiv ℝ (fderiv ℝ f) x v)‖ ≤ _
  rw [J.norm_map]
  exact (fderiv ℝ (fderiv ℝ f) x).le_opNorm v

/-- The derivative of an operator field applied to a scalar gradient has
the usual two-term operator norm bound. -/
theorem norm_fderiv_clm_gradient_le
    {A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hA : ContDiff ℝ ∞ A)
    (hf : ContDiff ℝ ∞ f) (x : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ (fun y => A y (_root_.gradient f y)) x‖ ≤
      ‖fderiv ℝ A x‖ * ‖fderiv ℝ f x‖ +
        ‖A x‖ * ‖fderiv ℝ (fderiv ℝ f) x‖ := by
  rw [fderiv_clm_apply (hA.differentiable (by simp) x)
    ((contDiff_euclidean_gradient hf).differentiable (by simp) x)]
  calc
    _ ≤ ‖(A x).comp (fderiv ℝ (_root_.gradient f) x)‖ +
        ‖(fderiv ℝ A x).flip (_root_.gradient f x)‖ := norm_add_le _ _
    _ ≤ ‖A x‖ * ‖fderiv ℝ (_root_.gradient f) x‖ +
        ‖fderiv ℝ A x‖ * ‖_root_.gradient f x‖ := by
      apply add_le_add ((A x).opNorm_comp_le _)
      simpa only [ContinuousLinearMap.opNorm_flip] using
        (fderiv ℝ A x).flip.le_opNorm (_root_.gradient f x)
    _ ≤ ‖A x‖ * ‖fderiv ℝ (fderiv ℝ f) x‖ +
        ‖fderiv ℝ A x‖ * ‖fderiv ℝ f x‖ := by
      rw [norm_euclidean_gradient_eq]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (norm_fderiv_euclidean_gradient_le hf x)
          (norm_nonneg (A x))) le_rfl
    _ = _ := by ring

/-- The trace of the derivative of a Euclidean vector field is bounded by
dimension times its operator norm. -/
theorem abs_divergence_le_mul_norm_fderiv
    {V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)} (hV : DifferentiableAt ℝ V x) :
    |∑ i, fderiv ℝ (fun y => V y i) x (EuclideanSpace.basisFun (Fin n) ℝ i)| ≤
      (n : ℝ) * ‖fderiv ℝ V x‖ := by
  have hcomp (i : Fin n) :
      fderiv ℝ (fun y => V y i) x (EuclideanSpace.basisFun (Fin n) ℝ i) =
        (fderiv ℝ V x (EuclideanSpace.basisFun (Fin n) ℝ i)) i := by
    have h := ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x hV.hasFDerivAt).fderiv
    exact congrArg (fun L => L (EuclideanSpace.basisFun (Fin n) ℝ i)) h
  calc
    _ ≤ ∑ i, |fderiv ℝ (fun y => V y i) x
        (EuclideanSpace.basisFun (Fin n) ℝ i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ‖fderiv ℝ V x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [hcomp, ← Real.norm_eq_abs]
      calc
        _ ≤ ‖fderiv ℝ V x (EuclideanSpace.basisFun (Fin n) ℝ i)‖ :=
          PiLp.norm_apply_le _ i
        _ ≤ ‖fderiv ℝ V x‖ * ‖EuclideanSpace.basisFun (Fin n) ℝ i‖ :=
          (fderiv ℝ V x).le_opNorm _
        _ = ‖fderiv ℝ V x‖ := by
          rw [(EuclideanSpace.basisFun (Fin n) ℝ).norm_eq_one, mul_one]
    _ = _ := by simp

end PoincareMT.HarmonicCoordinates

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

/-- A bound for the actual density-weighted metric Laplacian from ordinary
coefficient and scalar derivatives. -/
theorem abs_density_mul_laplacian_le (D : LeviCivitaData g)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin n)) :
    |g.pullbackVolumeDensity id x * D.laplacian f x| ≤
      (n : ℝ) * (‖fderiv ℝ g.euclideanDivergenceOperator x‖ * ‖fderiv ℝ f x‖ +
        ‖g.euclideanDivergenceOperator x‖ * ‖fderiv ℝ (fderiv ℝ f) x‖) := by
  rw [D.density_mul_laplacian_eq_divergenceOperator hf]
  exact (HarmonicCoordinates.abs_divergence_le_mul_norm_fderiv
    ((g.contDiff_euclideanDivergenceOperator.clm_apply
      (HarmonicCoordinates.contDiff_euclidean_gradient hf)).differentiable
        (by simp) x)).trans
    (mul_le_mul_of_nonneg_left
      (HarmonicCoordinates.norm_fderiv_clm_gradient_le
        g.contDiff_euclideanDivergenceOperator hf x) (Nat.cast_nonneg _))

/-- The retained gradient pairing is exactly the coefficient flux evaluated
by the ordinary scalar differential. -/
theorem density_mul_inner_gradient_eq_fderiv_divergenceOperator (D : LeviCivitaData g)
    (f u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    g.pullbackVolumeDensity id x * g.inner x (D.gradient f x) (D.gradient u x) =
      fderiv ℝ f x (g.euclideanDivergenceOperator x (_root_.gradient u x)) := by
  have hm : mvfderiv (𝓡 n) f x = fderiv ℝ f x := by
    ext v
    simp [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
    rfl
  rw [D.divergenceOperator_gradient, map_smul, smul_eq_mul, D.inner_gradient, hm]
  rfl

/-- Density-weighted gradient pairings need only the norm of the divergence
coefficient and the ordinary first derivatives. -/
theorem abs_density_mul_inner_gradient_le (D : LeviCivitaData g)
    (f u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    |g.pullbackVolumeDensity id x * g.inner x (D.gradient f x) (D.gradient u x)| ≤
      ‖g.euclideanDivergenceOperator x‖ * ‖fderiv ℝ f x‖ * ‖fderiv ℝ u x‖ := by
  rw [D.density_mul_inner_gradient_eq_fderiv_divergenceOperator, ← Real.norm_eq_abs]
  calc
    _ ≤ ‖fderiv ℝ f x‖ *
        ‖g.euclideanDivergenceOperator x (_root_.gradient u x)‖ :=
      (fderiv ℝ f x).le_opNorm _
    _ ≤ ‖fderiv ℝ f x‖ *
        (‖g.euclideanDivergenceOperator x‖ * ‖_root_.gradient u x‖) :=
      mul_le_mul_of_nonneg_left ((g.euclideanDivergenceOperator x).le_opNorm _)
        (norm_nonneg _)
    _ = _ := by rw [HarmonicCoordinates.norm_euclidean_gradient_eq]; ring

/-- Cutting off a scalar function introduces no second derivative of that
function in the density-weighted retained forcing estimate. -/
theorem abs_density_mul_laplacian_mul_le (D : LeviCivitaData g)
    {χ u : EuclideanSpace ℝ (Fin n) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hu : ContDiff ℝ ∞ u) (x : EuclideanSpace ℝ (Fin n)) :
    |g.pullbackVolumeDensity id x * D.laplacian (fun y => χ y * u y) x| ≤
      |χ x| * |g.pullbackVolumeDensity id x * D.laplacian u x| +
      |u x| * (n : ℝ) *
        (‖fderiv ℝ g.euclideanDivergenceOperator x‖ * ‖fderiv ℝ χ x‖ +
          ‖g.euclideanDivergenceOperator x‖ * ‖fderiv ℝ (fderiv ℝ χ) x‖) +
      2 * ‖g.euclideanDivergenceOperator x‖ * ‖fderiv ℝ χ x‖ * ‖fderiv ℝ u x‖ := by
  have heq : g.pullbackVolumeDensity id x * D.laplacian (fun y => χ y * u y) x =
      χ x * (g.pullbackVolumeDensity id x * D.laplacian u x) +
        u x * (g.pullbackVolumeDensity id x * D.laplacian χ x) +
        2 * (g.pullbackVolumeDensity id x *
          g.inner x (D.gradient χ x) (D.gradient u x)) := by
    rw [D.laplacian_mul (contMDiff_iff_contDiff.mpr hχ) (contMDiff_iff_contDiff.mpr hu)]
    ring
  rw [heq]
  calc
    _ ≤ |χ x| * |g.pullbackVolumeDensity id x * D.laplacian u x| +
        |u x| * |g.pullbackVolumeDensity id x * D.laplacian χ x| +
        2 * |g.pullbackVolumeDensity id x *
          g.inner x (D.gradient χ x) (D.gradient u x)| := by
      calc
        _ ≤ |χ x * (g.pullbackVolumeDensity id x * D.laplacian u x) +
              u x * (g.pullbackVolumeDensity id x * D.laplacian χ x)| +
            |2 * (g.pullbackVolumeDensity id x *
              g.inner x (D.gradient χ x) (D.gradient u x))| := abs_add_le _ _
        _ ≤ _ := by
          simpa only [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)] using
            add_le_add
              (abs_add_le (χ x * (g.pullbackVolumeDensity id x * D.laplacian u x))
                (u x * (g.pullbackVolumeDensity id x * D.laplacian χ x)))
              (le_refl |2 * (g.pullbackVolumeDensity id x *
                g.inner x (D.gradient χ x) (D.gradient u x))|)
    _ ≤ _ := by
      have hcut := mul_le_mul_of_nonneg_left (D.abs_density_mul_laplacian_le hχ x)
        (abs_nonneg (u x))
      have hcross := mul_le_mul_of_nonneg_left (D.abs_density_mul_inner_gradient_le χ u x)
        (show (0 : ℝ) ≤ 2 by norm_num)
      calc
        _ ≤ |χ x| * |g.pullbackVolumeDensity id x * D.laplacian u x| +
            |u x| * ((n : ℝ) *
              (‖fderiv ℝ g.euclideanDivergenceOperator x‖ * ‖fderiv ℝ χ x‖ +
                ‖g.euclideanDivergenceOperator x‖ * ‖fderiv ℝ (fderiv ℝ χ) x‖)) +
            2 * (‖g.euclideanDivergenceOperator x‖ *
              ‖fderiv ℝ χ x‖ * ‖fderiv ℝ u x‖) :=
          add_le_add (add_le_add le_rfl hcut) hcross
        _ = _ := by ring

end PoincareMT.LeviCivitaData
