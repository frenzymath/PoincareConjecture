import PoincareConjecture.Proofs.M35.Uniqueness.CoordinateRotations
import PoincareConjecture.Proofs.M35.Uniqueness.AxisRotations

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology Matrix

namespace PoincareConjecture.M35.Uniqueness

theorem linear_killing_path_preserves_metric {n : ℕ}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (D : LeviCivitaData g)
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (ρ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hzero : ∀ x, ρ 0 x = x)
    (hvelocity : ∀ s x, HasDerivAt (fun t => ρ t x) (B (ρ s x)) s)
    (hkill : ∀ x u v, DeTurckNative.metricLieDerivative D (fun y => B y) x u v = 0)
    (s : ℝ) (x u v : EuclideanSpace ℝ (Fin n)) :
    g.inner (ρ s x) (ρ s u) (ρ s v) = g.inner x u v := by
  have hd (t : ℝ) : HasDerivAt (fun r => g.inner (ρ r x) (ρ r u) (ρ r v)) 0 t := by
    have hG := ((g.contDiffAt_euclideanCoefficients (ρ t x)).differentiableAt
      (by simp)).hasFDerivAt
    have hg := hG.comp_hasDerivAt t (hvelocity t x)
    have hp₁ := hg.clm_apply (hvelocity t u)
    have hp := hp₁.clm_apply (hvelocity t v)
    have hf₁ := hG.clm_apply (hasFDerivAt_const (ρ t u) (ρ t x))
    have hf := hf₁.clm_apply (hasFDerivAt_const (ρ t v) (ρ t x))
    change HasFDerivAt (fun y => g.inner y (ρ t u) (ρ t v)) _ (ρ t x) at hf
    have he : fderiv ℝ (fun y => g.inner y (ρ t u) (ρ t v)) (ρ t x) (B (ρ t x)) =
        fderiv ℝ g.euclideanCoefficients (ρ t x) (B (ρ t x)) (ρ t u) (ρ t v) := by
      simpa using congrArg (fun L => L (B (ρ t x))) hf.fderiv
    have hk := hkill (ρ t x) (ρ t u) (ρ t v)
    rw [metricLieDerivative_linear, he] at hk
    simp only [Function.comp_apply, add_apply] at hp
    exact hp.congr_deriv hk
  have hz := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (C := 0) (fun t (_ : t ∈ (univ : Set ℝ)) => (hd t).hasDerivWithinAt)
    (fun t _ => by simp) (mem_univ 0) (mem_univ s)
  have heq : g.inner (ρ s x) (ρ s u) (ρ s v) = g.inner (ρ 0 x) (ρ 0 u) (ρ 0 v) := by
    simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hz
  change g.euclideanCoefficients (ρ s x) (ρ s u) (ρ s v) =
    g.euclideanCoefficients (ρ 0 x) (ρ 0 u) (ρ 0 v) at heq
  change g.euclideanCoefficients (ρ s x) (ρ s u) (ρ s v) =
    g.euclideanCoefficients x u v
  simpa only [hzero] using heq

theorem coordinateRotation_hasDerivAt_time (s : ℝ) (x : StandardCapSpace) :
    HasDerivAt (fun t => standardRotation (coordinateRotation t) x)
      (coordinateRotationGenerator (standardRotation (coordinateRotation s) x)) s := by
  let f : ℝ → Fin 3 → ℝ := fun t =>
    ![Real.cos t * x 0 - Real.sin t * x 1,
      Real.sin t * x 0 + Real.cos t * x 1, x 2]
  have hf : HasDerivAt f
      ![-Real.sin s * x 0 - Real.cos s * x 1,
        Real.cos s * x 0 - Real.sin s * x 1, 0] s := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact ((Real.hasDerivAt_cos s).mul_const (x 0)).sub
        ((Real.hasDerivAt_sin s).mul_const (x 1))
    · simpa [f, sub_eq_add_neg, neg_mul] using!
        ((Real.hasDerivAt_sin s).mul_const (x 0)).add
          ((Real.hasDerivAt_cos s).mul_const (x 1))
    · exact hasDerivAt_const s (x 2)
  let L := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm
  have h := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s hf
  convert! h using 1
  · funext t
    ext i
    fin_cases i <;>
      simp [standardRotation, coordinateRotation, f, L,
        dotProduct, Fin.sum_univ_succ, sub_eq_add_neg]
  · ext i
    fin_cases i <;>
      simp [coordinateRotationGenerator, standardRotation, coordinateRotation, L,
        Matrix.toEuclideanLin, dotProduct, Fin.sum_univ_succ] <;> ring

theorem coordinateRotation_isometry_of_killing {g : RiemannianMetric 3 StandardCapSpace}
    (D : LeviCivitaData g)
    (hkill : ∀ x u v, DeTurckNative.metricLieDerivative D
      (fun y => coordinateRotationGenerator y) x u v = 0)
    (s : ℝ) (x u v : StandardCapSpace) :
    g.inner (standardRotation (coordinateRotation s) x)
      (standardRotation (coordinateRotation s) u) (standardRotation (coordinateRotation s) v) =
        g.inner x u v :=
  linear_killing_path_preserves_metric D coordinateRotationGenerator
    (fun t => standardRotation (coordinateRotation t))
    (fun x => by rw [coordinateRotation_zero, standardRotation_one])
    coordinateRotation_hasDerivAt_time hkill s x u v

end PoincareConjecture.M35.Uniqueness
