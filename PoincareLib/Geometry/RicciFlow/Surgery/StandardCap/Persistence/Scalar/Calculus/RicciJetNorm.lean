import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Homothety
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Scalar.Calculus.ScalarJet

/-!
# The squared Ricci norm from bounded elliptic metric jets

Reconstruct the actual Ricci bilinear form from its fixed coordinate
components. Ellipticity bounds every metric-orthonormal vector in the
coordinate norm, giving a uniform bound for the full squared Ricci norm.
Morgan--Tian, equation (3.7), p. 41, and Lemma 16.8, pp. 372-373;
see derivation 26.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The native two-jet contains four nested continuous-linear slots.
set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareMT.M44

open PoincareMT.SpacetimeBounds

local notation "E" n:max => EuclideanSpace ℝ (Fin n)

/-- The Ricci bilinear form reconstructed from the native two-jet.
Its coefficients are taken in a fixed Euclidean orthonormal basis.
Source: the Ricci term in equation (3.7), p. 41. -/
noncomputable def jetRicciBilinear {n : ℕ} (J : MetricTwoJet n) : MetricCoefficient n :=
  ∑ i, ∑ j, jetRicci J (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j) •
      (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)).smulRight
        (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j))

/-- The reconstructed form is the actual Ricci tensor.
Source: equation (3.7), p. 41. -/
theorem jetRicciBilinear_metricTwoJet {n : ℕ}
    {g : RiemannianMetric n (E n)} (D : LeviCivitaData g) (x : E n) :
    jetRicciBilinear (metricTwoJet g.euclideanCoefficients x) =
      (show E n →ₗ[ℝ] E n →ₗ[ℝ] ℝ from M13.ricciLinear D x).toContinuousBilinearMap := by
  unfold jetRicciBilinear
  simp_rw [jetRicci_metricTwoJet D]
  exact (bilinear_eq_sum_dual (EuclideanSpace.basisFun (Fin n) ℝ)
    (show E n →ₗ[ℝ] E n →ₗ[ℝ] ℝ from M13.ricciLinear D x).toContinuousBilinearMap).symm

/-- The native Ricci bilinear form is smooth on invertible two-jets.
Source: the finite-jet calculation in Lemma 16.8, pp. 372-373. -/
theorem contDiffAt_jetRicciBilinear {n : ℕ} {J : MetricTwoJet n}
    (hJ : J.1.IsInvertible) : ContDiffAt ℝ ∞ (@jetRicciBilinear n) J := by
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (contDiffAt_jetRicci hJ _ _).smul contDiffAt_const

/-- Ellipticity bounds the full metric squared norm of any bilinear
form by its coordinate operator norm. This includes all off-diagonal
entries of the contract's norm. Source: equation (3.7), p. 41. -/
theorem bilinear_metric_norm_sq_le {n : ℕ} (g : RiemannianMetric n (E n))
    (x : E n) (B : MetricCoefficient n) {a : ℝ} (ha : 0 < a)
    (hell : ∀ v : E n, a * ‖v‖ ^ 2 ≤ g.inner x v v) :
    (∑ i, ∑ j, (B (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2) ≤
      (n : ℝ) ^ 2 * (‖B‖ / a) ^ 2 := by
  have hunit (i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      g.inner x (g.orthonormalBasis x i) (g.orthonormalBasis x i) = 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : E n → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change inner ℝ (g.orthonormalBasis x i) (g.orthonormalBasis x i) = 1
    rw [real_inner_self_eq_norm_sq, (g.orthonormalBasis x).norm_eq_one]
    norm_num
  have hterm (i j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      (B (g.orthonormalBasis x i) (g.orthonormalBasis x j)) ^ 2 ≤ (‖B‖ / a) ^ 2 := by
    let u : E n := g.orthonormalBasis x i
    let v : E n := g.orthonormalBasis x j
    have hi := hell u
    have hj := hell v
    change a * ‖u‖ ^ 2 ≤ g.inner x (g.orthonormalBasis x i) (g.orthonormalBasis x i) at hi
    change a * ‖v‖ ^ 2 ≤ g.inner x (g.orthonormalBasis x j) (g.orthonormalBasis x j) at hj
    rw [hunit] at hi hj
    have hp : a * ‖u‖ * ‖v‖ ≤ 1 := by
      nlinarith [mul_nonneg ha.le (sq_nonneg (‖u‖ - ‖v‖))]
    have hB : |B u v| ≤ ‖B‖ / a := by
      apply (le_div_iff₀ ha).mpr
      calc
        _ ≤ (‖B‖ * ‖u‖ * ‖v‖) * a :=
          mul_le_mul_of_nonneg_right (B.le_opNorm₂ _ _) ha.le
        _ = ‖B‖ * (a * ‖u‖ * ‖v‖) := by ring
        _ ≤ ‖B‖ * 1 := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
        _ = _ := mul_one _
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _)
      (div_nonneg (norm_nonneg _) ha.le)).mpr hB
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n := by
    unfold TangentSpace
    simp
  calc
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)),
        ∑ _j : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x)), (‖B‖ / a) ^ 2 :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = _ := by simp [hdim]; ring

/-- The actual squared Ricci norm has a uniform coordinate bound
from the two-jet and a positive ellipticity constant.
Source: equation (3.7), p. 41. -/
theorem ricciNormSq_le_jetRicciBilinear {n : ℕ}
    {g : RiemannianMetric n (E n)} (D : LeviCivitaData g) (x : E n)
    {a : ℝ} (ha : 0 < a) (hell : ∀ v : E n, a * ‖v‖ ^ 2 ≤ g.inner x v v) :
    D.ricciNormSq x ≤ (n : ℝ) ^ 2 *
      (‖jetRicciBilinear (metricTwoJet g.euclideanCoefficients x)‖ / a) ^ 2 := by
  rw [jetRicciBilinear_metricTwoJet D]
  exact bilinear_metric_norm_sq_le g x
    (show E n →ₗ[ℝ] E n →ₗ[ℝ] ℝ from M13.ricciLinear D x).toContinuousBilinearMap ha hell

end PoincareMT.M44
