import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Regularity.Sobolev
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Composition
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Scaling
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv








noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal NNReal

namespace PoincareConjecture.LeviCivitaData

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

omit [IsManifold (𝓡 n) ∞ M] in

theorem contMDiff_rpow_of_pos {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x) (p : ℝ) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => f x ^ p) := by
  intro x
  exact (Real.contDiffAt_rpow_const_of_ne (hpos x).ne').contMDiffAt.comp x (hf x)


theorem gradient_rpow_of_pos (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x) (p : ℝ) (x : M) :
    D.gradient (fun y => f y ^ p) x = (p * f x ^ (p - 1)) • D.gradient f x := by
  simpa only [Real.deriv_rpow_const, Function.comp_def] using
    D.gradient_comp ((hf x).mdifferentiableAt (by simp))
      (Real.hasDerivAt_rpow_const (p := p) (Or.inl (hpos x).ne')).differentiableAt


theorem hessian_rpow_of_pos (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x) (p : ℝ)
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    D.hessian (fun y => f y ^ p) x v w =
      (p * f x ^ (p - 1)) * D.hessian f x v w +
        (p * (p - 1) * f x ^ (p - 2)) * mvfderiv (𝓡 n) f x v * mvfderiv (𝓡 n) f x w := by
  have hp := contMDiff_rpow_of_pos hf hpos p
  have hpm := contMDiff_rpow_of_pos hf hpos (p - 1)
  have hdf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => p * f y ^ (p - 1)) :=
    contMDiff_const.mul hpm
  have heq : D.gradient (fun y => f y ^ p) =
      (fun y => p * f y ^ (p - 1)) • D.gradient f :=
    funext fun y => D.gradient_rpow_of_pos hf hpos p y
  rw [D.hessian_eq_inner_connection_gradient (hp x), heq,
    D.connection.isCovariantDerivativeOn.leibniz
      ((D.contMDiffAt_gradient (hf x)).mdifferentiableAt (by simp))
      ((hdf x).mdifferentiableAt (by simp)),
    D.hessian_eq_inner_connection_gradient (hf x)]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul, smul_eq_mul, D.inner_gradient]
  rw [mvfderiv_const_mul, ← D.inner_gradient (fun y => f y ^ (p - 1)) x v,
    D.gradient_rpow_of_pos hf hpos]
  simp only [map_smul, smul_apply, smul_eq_mul, D.inner_gradient,
    show p - 1 - 1 = p - 2 by ring]
  ring


theorem laplacian_rpow_of_pos (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x) (p : ℝ) (x : M) :
    D.laplacian (fun y => f y ^ p) x =
      (p * f x ^ (p - 1)) * D.laplacian f x +
        (p * (p - 1) * f x ^ (p - 2)) *
          g.inner x (D.gradient f x) (D.gradient f x) := by
  unfold laplacian
  simp_rw [D.hessian_rpow_of_pos hf hpos p]
  simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  rw [D.sum_mvfderiv_mul_eq_inner_gradient]



theorem laplacian_rpow_lower (D : LeviCivitaData g) {f : M → ℝ}
    (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) (hpos : ∀ x, 0 < f x)
    {p κ : ℝ} (hp : 1 ≤ p) (x : M) (hlap : -κ * f x ≤ D.laplacian f x) :
    -(p * κ) * f x ^ p ≤ D.laplacian (fun y => f y ^ p) x := by
  have hgrad0 : 0 ≤ g.inner x (D.gradient f x) (D.gradient f x) := by
    by_cases h : D.gradient f x = 0
    · simp [h]
    · exact (g.pos x _ h).le
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hprod : f x ^ (p - 1) * f x = f x ^ p := by
    rw [← Real.rpow_add_one (hpos x).ne', sub_add_cancel]
  have hfirst := mul_le_mul_of_nonneg_left hlap
    (mul_nonneg hp0 (Real.rpow_nonneg (hpos x).le (p - 1)))
  have heq : (p * f x ^ (p - 1)) * (-κ * f x) = -(p * κ) * f x ^ p := by
    rw [← hprod]
    ring
  rw [heq] at hfirst
  rw [D.laplacian_rpow_of_pos hf hpos]
  exact hfirst.trans (le_add_of_nonneg_right (mul_nonneg
    (mul_nonneg (mul_nonneg hp0 (sub_nonneg.mpr hp))
      (Real.rpow_nonneg (hpos x).le _)) hgrad0))

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.HarmonicCoordinates

variable {n : ℕ}



theorem exists_uniform_subsolution_power_sobolev (hn : 2 ≤ n)
    (R : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ q : ℝ≥0, 2 < q ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g),
        (∀ x ∈ Metric.ball 0 R, ∀ v : EuclideanSpace ℝ (Fin n),
          a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v ∧
            g.euclideanCoefficients x v v ≤ b * ‖v‖ ^ 2) →
        ∀ η f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ η → ContDiff ℝ ∞ f →
          HasCompactSupport η → tsupport η ⊆ Metric.ball 0 R → (∀ x, 0 < f x) →
        ∀ p κ : ℝ, 1 ≤ p → (∀ x ∈ tsupport η, -κ * f x ≤ D.laplacian f x) →
          (eLpNorm (fun x => η x * f x ^ p) q volume).toReal ^ 2 ≤ C *
            ((p * κ) * (∫ x, η x ^ 2 * (f x ^ p) ^ 2 ∂g.volumeMeasure) +
              ∫ x, (f x ^ p) ^ 2 *
                g.inner x (D.gradient η x) (D.gradient η x) ∂g.volumeMeasure) := by
  obtain ⟨q, hq, C, hC, hSob⟩ := exists_uniform_cutoff_sobolev hn R ha hb
  refine ⟨q, hq, C, hC, fun g D hell η f hη hf hηc hηs hpos p κ hp hlap => ?_⟩
  have hfs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f := contMDiff_iff_contDiff.mpr hf
  apply hSob g D hell η (fun x => f x ^ p) hη
    (contMDiff_iff_contDiff.mp (LeviCivitaData.contMDiff_rpow_of_pos hfs hpos p)) hηc hηs
  intro x hx
  have h := mul_le_mul_of_nonneg_left (D.laplacian_rpow_lower hfs hpos hp x (hlap x hx))
    (Real.rpow_nonneg (hpos x).le p)
  nlinarith only [h]

end PoincareConjecture.HarmonicCoordinates
