import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_ScalarJet

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 12

open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M44

open PoincareConjecture.SpacetimeBounds

local notation "E" n:max => EuclideanSpace ℝ (Fin n)

noncomputable def jetRicciBilinear {n : ℕ} (J : MetricTwoJet n) : MetricCoefficient n :=
  ∑ i, ∑ j, jetRicci J (EuclideanSpace.basisFun (Fin n) ℝ i)
    (EuclideanSpace.basisFun (Fin n) ℝ j) •
      (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)).smulRight
        (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ j))

theorem jetRicciBilinear_metricTwoJet {n : ℕ}
    {g : RiemannianMetric n (E n)} (D : LeviCivitaData g) (x : E n) :
    jetRicciBilinear (metricTwoJet g.euclideanCoefficients x) =
      (show E n →ₗ[ℝ] E n →ₗ[ℝ] ℝ from M13.ricciLinear D x).toContinuousBilinearMap := by
  unfold jetRicciBilinear
  simp_rw [jetRicci_metricTwoJet D]
  exact (bilinear_eq_sum_dual (EuclideanSpace.basisFun (Fin n) ℝ)
    (show E n →ₗ[ℝ] E n →ₗ[ℝ] ℝ from M13.ricciLinear D x).toContinuousBilinearMap).symm

theorem contDiffAt_jetRicciBilinear {n : ℕ} {J : MetricTwoJet n}
    (hJ : J.1.IsInvertible) : ContDiffAt ℝ ∞ (@jetRicciBilinear n) J := by
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  exact (contDiffAt_jetRicci hJ _ _).smul contDiffAt_const

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

theorem ricciNormSq_le_jetRicciBilinear {n : ℕ}
    {g : RiemannianMetric n (E n)} (D : LeviCivitaData g) (x : E n)
    {a : ℝ} (ha : 0 < a) (hell : ∀ v : E n, a * ‖v‖ ^ 2 ≤ g.inner x v v) :
    D.ricciNormSq x ≤ (n : ℝ) ^ 2 *
      (‖jetRicciBilinear (metricTwoJet g.euclideanCoefficients x)‖ / a) ^ 2 := by
  rw [jetRicciBilinear_metricTwoJet D]
  exact bilinear_metric_norm_sq_le g x
    (show E n →ₗ[ℝ] E n →ₗ[ℝ] ℝ from M13.ricciLinear D x).toContinuousBilinearMap ha hell

end PoincareConjecture.M44
