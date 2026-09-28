import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.EnergyBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Elliptic.Dirichlet.CoordinateWeakDerivative

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter UniformSpace
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.HarmonicCoordinates

open LeviCivitaData.Dirichlet

theorem coordinateDerivative_refl_norm_sq_le_of_ellipticity
    {n : ℕ} {R a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (hell : ∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
      a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
        g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : Ω ⊆ Metric.ball 0 R)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsCompact S)
    (v : EuclideanSpace ℝ (Fin n)) (u : H1Zero D Ω) :
    ‖coordinateDerivative (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n)))
      contMDiffOn_id contMDiffOn_id hS (by simp) v u‖ ^ 2 ≤
      (b / Real.sqrt (a ^ n)) * ‖v‖ ^ 2 * ‖u‖ ^ 2 := by
  let T := coordinateDerivative (D := D) (Ω := Ω)
    (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n)))
    contMDiffOn_id contMDiffOn_id hS (by simp) v
  change ‖T u‖ ^ 2 ≤ _
  induction u using Completion.induction_on with
  | hp =>
    exact isClosed_le (T.continuous.norm.pow 2)
      (continuous_const.mul (continuous_norm.pow 2))
  | ih f =>
    change ‖coordinateDerivative _ _ _ _ _ _ (f : H1Zero D Ω)‖ ^ 2 ≤ _
    rw [coordinateDerivative_coe, Completion.norm_coe]
    change ‖(EnergyTest.coordinateDerivative_memLp
      (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n)))
      contMDiffOn_id hS (by simp) v f).toLp _‖ ^ 2 ≤ _
    rw [Poincare.Analysis.Sobolev.norm_toLp_sq_eq_integral]
    change (∫ x in S, (fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x v) ^ 2) ≤ _
    have hf : ContDiff ℝ ∞ (f : EuclideanSpace ℝ (Fin n) → ℝ) :=
      contMDiff_iff_contDiff.mp f.smooth
    have hdi : Integrable (fun x => ‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ ^ 2)
        volume :=
      ((hf.continuous_fderiv (by simp)).norm.memLp_of_hasCompactSupport
        (f.hasCompactSupport.fderiv ℝ).norm).integrable_sq
    have henergy := integral_fderiv_sq_le_of_ellipticity D ha hb hell hf
      f.hasCompactSupport (f.support_subset.trans hΩ)
    have hnorm : (∫ x, g.inner x (D.gradient f x) (D.gradient f x) ∂g.volumeMeasure) ≤
        ‖f‖ ^ 2 := by
      rw [f.norm_sq]
      exact le_add_of_nonneg_left (integral_nonneg fun x => mul_self_nonneg (f x))
    calc
      _ ≤ ∫ x in S, ‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ ^ 2 * ‖v‖ ^ 2 := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
          (hdi.integrableOn.mul_const _) (Eventually.of_forall fun x => ?_)
        have h := (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg v))).mpr
            ((fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x).le_opNorm v)
        simpa only [Real.norm_eq_abs, sq_abs, mul_pow] using h
      _ = (∫ x in S, ‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ ^ 2) * ‖v‖ ^ 2 :=
        integral_mul_const _ _
      _ ≤ (∫ x, ‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ ^ 2) * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right
          (setIntegral_le_integral hdi (Eventually.of_forall fun x => sq_nonneg _)) (sq_nonneg _)
      _ ≤ ((b / Real.sqrt (a ^ n)) *
          ∫ x, g.inner x (D.gradient f x) (D.gradient f x) ∂g.volumeMeasure) * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right henergy (sq_nonneg _)
      _ ≤ ((b / Real.sqrt (a ^ n)) * ‖f‖ ^ 2) * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hnorm (div_nonneg hb (Real.sqrt_nonneg _))) (sq_nonneg _)
      _ = _ := by ring

theorem coordinateDerivative_refl_opNorm_le_of_ellipticity
    {n : ℕ} {R a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (hell : ∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
      a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
        g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : Ω ⊆ Metric.ball 0 R)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsCompact S)
    (v : EuclideanSpace ℝ (Fin n)) :
    ‖coordinateDerivative (D := D) (Ω := Ω)
      (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n)))
      contMDiffOn_id contMDiffOn_id hS (by simp) v‖ ≤
      Real.sqrt (b / Real.sqrt (a ^ n)) * ‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hb (Real.sqrt_nonneg _))]
  exact coordinateDerivative_refl_norm_sq_le_of_ellipticity ha hb D hell hΩ hS v u

theorem localCoordinateDerivative_refl_norm_sq_le_of_ellipticity
    {n : ℕ} {R a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (hell : ∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
      a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
        g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : Ω ⊆ Metric.ball 0 R)
    {S O : Set (EuclideanSpace ℝ (Fin n))} (hS : IsCompact S) (hOS : O ⊆ S)
    (v : EuclideanSpace ℝ (Fin n)) (u : H1Zero D Ω) :
    ‖localCoordinateDerivative (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n)))
      contMDiffOn_id contMDiffOn_id hS (by simp) hOS v u‖ ^ 2 ≤
      (b / Real.sqrt (a ^ n)) * ‖v‖ ^ 2 * ‖u‖ ^ 2 := by
  let T := coordinateDerivative (D := D) (Ω := Ω)
    (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n)))
    contMDiffOn_id contMDiffOn_id hS (by simp) v
  let J : Lp ℝ 2 (volume.restrict S) →L[ℝ] Lp ℝ 2 (volume.restrict O) :=
    Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
      (by simpa only [one_smul] using Measure.restrict_mono hOS (le_refl volume))
  have hJ : ‖J‖ ≤ 1 := by
    simpa only [ENNReal.toReal_one, Real.one_rpow] using
      Lp.norm_LpToLpOfMeasureLeSMul_le (p := 2) (E := ℝ) (c := 1) (by simp)
        (by simpa only [one_smul] using Measure.restrict_mono hOS (le_refl volume))
  change ‖J (T u)‖ ^ 2 ≤ _
  calc
    _ ≤ ‖T u‖ ^ 2 := by
      apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      exact (J.le_opNorm _).trans (by simpa using mul_le_mul_of_nonneg_right hJ (norm_nonneg (T u)))
    _ ≤ _ := coordinateDerivative_refl_norm_sq_le_of_ellipticity ha hb D hell hΩ hS v u

end PoincareConjecture.HarmonicCoordinates
