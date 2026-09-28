import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.MetricEntropyTest
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Maximum.L2IntegralVariation









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped ContDiff Manifold

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

local instance metricPotentialCovectorGroup : NormedAddCommGroup (V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance metricPotentialCovectorSpace : NormedSpace ℝ (V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance metricPotentialBilinearGroup : NormedAddCommGroup (V →L[ℝ] V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance metricPotentialBilinearSpace : NormedSpace ℝ (V →L[ℝ] V →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem normBoundEntropy_affine {Q s : ℝ} (hs : Q + 1 ≤ s) :
    normBoundEntropy Q s = normBoundEntropy Q (Q + 1) + (s - (Q + 1)) := by
  have hc : Continuous (fun u : ℝ => Real.smoothTransition (u - Q)) :=
    Real.smoothTransition.continuous.comp (continuous_id.sub continuous_const)
  have ha := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) Q (Q + 1))
    (hc.intervalIntegrable (μ := volume) (Q + 1) s)
  have he : (∫ u in (Q + 1)..s, Real.smoothTransition (u - Q)) = s - (Q + 1) := by
    calc
      _ = ∫ _u in (Q + 1)..s, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hs] at hu
        exact Real.smoothTransition.one_of_one_le (by linarith only [hu.1])
      _ = _ := by simp
  change (∫ u in Q..s, Real.smoothTransition (u - Q)) = _
  rw [← ha, he]
  rfl

def metricEntropyPotential (g : RiemannianMetric n V) (η : V → ℝ) (Q : ℝ)
    (p : V × V) : ℝ :=
  (η p.1 * g.pullbackVolumeDensity id p.1) * normBoundEntropy Q (g.inner p.1 p.2 p.2)

theorem metricEntropyPotential_contDiff (g : RiemannianMetric n V) {η : V → ℝ}
    (hη : ContDiff ℝ ∞ η) (Q : ℝ) : ContDiff ℝ ∞ (metricEntropyPotential g η Q) :=
  ((hη.mul (raw_volumeDensity_contDiff g)).comp contDiff_fst).mul
    ((normBoundEntropy_contDiff Q).comp (metric_quadratic_contDiff g))

theorem metricEntropyPotential_value_hasFDerivAt (g : RiemannianMetric n V)
    (η : V → ℝ) (Q : ℝ) (x z : V) :
    HasFDerivAt (fun w => metricEntropyPotential g η Q (x, w))
      ((2 * η x * g.pullbackVolumeDensity id x *
        Real.smoothTransition (g.inner x z z - Q)) • g.euclideanCoefficients x z) z := by
  have hq := (g.euclideanCoefficients x).hasFDerivAt.clm_apply (hasFDerivAt_id z)
  have hφ := (normBoundEntropy_hasDerivAt Q (g.inner x z z)).comp_hasFDerivAt
    (f := fun w : V => g.euclideanCoefficients x w w) z (by simpa only [id_eq] using! hq)
  have h := hφ.const_mul (η x * g.pullbackVolumeDensity id x)
  convert! h using 1
  ext w
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, add_apply, ContinuousLinearMap.flip_apply]
  have hs : g.euclideanCoefficients x w z = g.euclideanCoefficients x z w := g.symm x w z
  rw [hs]
  ring

theorem metricEntropyPotential_value_test (g : RiemannianMetric n V)
    (η : V → ℝ) (Q : ℝ) (x z e : V) :
    fderiv ℝ (fun w => metricEntropyPotential g η Q (x, w)) z e =
      metricEntropyTest g η Q e (x, z) := by
  rw [(metricEntropyPotential_value_hasFDerivAt g η Q x z).fderiv]
  simp only [metricEntropyTest, metricEntropyLinear, smul_apply, smul_eq_mul]
  have hs : g.euclideanCoefficients x z e = g.euclideanCoefficients x e z := g.symm x z e
  rw [hs]
  ring

private def weightedMetricBilin (g : RiemannianMetric n V) (η : V → ℝ)
    (x : V) : V →L[ℝ] V →L[ℝ] ℝ :=
  η x • (g.pullbackVolumeDensity id x • g.euclideanCoefficients x)

private theorem weightedMetricBilin_bound (g : RiemannianMetric n V)
    {η : V → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) :
    ∃ C : ℝ, ∀ x, ‖weightedMetricBilin g η x‖ ≤ C := by
  have hBc : HasCompactSupport (weightedMetricBilin g η) := by
    apply hc.mono'
    intro x hx
    by_contra hn
    apply hx
    change η x • (g.pullbackVolumeDensity id x • g.euclideanCoefficients x) = 0
    rw [image_eq_zero_of_notMem_tsupport hn, zero_smul]
  have hBs : ContDiff ℝ ∞ (weightedMetricBilin g η) :=
    hη.smul ((raw_volumeDensity_contDiff g).smul
      (contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients))
  exact HasCompactSupport.exists_bound_of_continuous
    (f := weightedMetricBilin g η) hBc hBs.continuous

private theorem weighted_metric_quadratic_bound (g : RiemannianMetric n V)
    {η : V → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x z : V),
      ‖(η x * g.pullbackVolumeDensity id x) * g.inner x z z‖ ≤ C * ‖z‖ ^ 2 := by
  let B := weightedMetricBilin g η
  obtain ⟨C, hC⟩ := weightedMetricBilin_bound g hη hc
  refine ⟨C, (norm_nonneg (B 0)).trans (hC 0), ?_⟩
  intro x z
  have he : (η x * g.pullbackVolumeDensity id x) * g.inner x z z = B x z z := by
    change (η x * g.pullbackVolumeDensity id x) * g.euclideanCoefficients x z z =
      η x * (g.pullbackVolumeDensity id x * g.euclideanCoefficients x z z)
    ring
  rw [he]
  calc
    _ ≤ ‖B x z‖ * ‖z‖ := (B x z).le_opNorm z
    _ ≤ (‖B x‖ * ‖z‖) * ‖z‖ :=
      mul_le_mul_of_nonneg_right ((B x).le_opNorm z) (norm_nonneg _)
    _ = ‖B x‖ * ‖z‖ ^ 2 := by ring
    _ ≤ C * ‖z‖ ^ 2 := mul_le_mul_of_nonneg_right (hC x) (sq_nonneg _)

theorem metricEntropyPotential_quadratic_bound (g : RiemannianMetric n V)
    {η : V → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    {Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x z, ‖metricEntropyPotential g η Q (x, z)‖ ≤ C * ‖z‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := weighted_metric_quadratic_bound g hη hc
  refine ⟨C, hC, fun x z => ?_⟩
  have hq : 0 ≤ g.inner x z z := by
    by_cases hz : z = 0
    · simp [hz]
    · exact (g.pos x z hz).le
  have hφ : ‖normBoundEntropy Q (g.inner x z z)‖ ≤ ‖g.inner x z z‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (normBoundEntropy_nonneg _ _),
      Real.norm_eq_abs, abs_of_nonneg hq]
    exact normBoundEntropy_le hQ hq
  calc
    _ ≤ ‖(η x * g.pullbackVolumeDensity id x) * g.inner x z z‖ := by
      simp only [metricEntropyPotential, norm_mul]
      exact mul_le_mul_of_nonneg_left hφ (by positivity)
    _ ≤ C * ‖z‖ ^ 2 := hb x z

theorem metricEntropyPotential_integrable (g : RiemannianMetric n V)
    {η : V → ℝ} (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    {Q : ℝ} (hQ : 0 ≤ Q) (u : Lp V 2 (volume : Measure V)) :
    Integrable (fun x => metricEntropyPotential g η Q (x, u x)) := by
  obtain ⟨C, _, hC⟩ := metricEntropyPotential_quadratic_bound g hη hc hQ
  exact integrable_quadratic_field _ (metricEntropyPotential_contDiff g hη Q).continuous hC u

end PoincareConjecture.M35.Uniqueness.Heat
