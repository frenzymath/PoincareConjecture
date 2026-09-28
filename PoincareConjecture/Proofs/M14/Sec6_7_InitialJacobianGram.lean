import PoincareConjecture.Proofs.M14.Sec6_7_InitialJacobianPair
import PoincareConjecture.Proofs.M14.Sec6_7_ExponentialGram











set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem metric_pair_transport {q r : G.Point} (h : q = r)
    (v w : G.Horizontal q) :
    G.spacetime.horizontalMetric.inner q v w =
      G.spacetime.horizontalMetric.inner r (h ▸ v) (h ▸ w) := by
  cases h
  rfl




theorem tendsto_exponentialGram_scaled_zero
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (b₀ : Module.Basis (Fin n) ℝ (G.Horizontal x))
    (horth : ∀ i j, G.spacetime.horizontalMetric.inner x (b₀ i) (b₀ j) =
      if i = j then 1 else 0)
    {Z : G.Horizontal x} {b : ℝ} (hb : (Z, b) ∈ E.domain) (hpos : 0 < b) :
    Tendsto (fun s : ℝ => (s⁻¹) ^ 2 • exponentialGram E b₀ Z s) (𝓝[>] (0 : ℝ))
      (𝓝 ((4 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))) := by
  let P := exponentialInitialValuePath E Z b hb hpos
  let Q := fun i => initialValuePath_differentialData hM04 hM12 P (b₀ i)
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  change Tendsto (fun s => (s⁻¹) ^ 2 * exponentialGram E b₀ Z s i j) _
    (𝓝 (4 * (if i = j then (1 : ℝ) else 0)))
  have hlim := tendsto_initialJacobi_scaled_pair hM12 P.square_path (Q i) (Q j)
    (initialValuePath_differentialField_zero hM04 hM12 P (b₀ i))
    (initialValuePath_differentialField_zero hM04 hM12 P (b₀ j))
  obtain ⟨hi, hdi⟩ := initialValuePath_differential_initialDerivative hM04 hM12 P (b₀ i)
  obtain ⟨hj, hdj⟩ := initialValuePath_differential_initialDerivative hM04 hM12 P (b₀ j)
  have hvalue : G.spacetime.horizontalMetric.inner (P.square_path.curve 0)
      (M14JacobiFirstDerivative (Q i) 0) (M14JacobiFirstDerivative (Q j) 0) =
        4 * G.spacetime.horizontalMetric.inner x (b₀ i) (b₀ j) := by
    have h := metric_pair_transport hi
      (M14JacobiFirstDerivative (Q i) 0) (M14JacobiFirstDerivative (Q j) 0)
    rw [hdi, show hi ▸ M14JacobiFirstDerivative (Q j) 0 = (2 : ℝ) • b₀ j from hdj] at h
    simp only [map_smul, smul_apply, smul_eq_mul] at h
    nlinarith only [h]
  rw [hvalue, horth] at hlim
  apply hlim.congr'
  filter_upwards [Ioc_mem_nhdsGT hpos] with s hs
  have hsC : s ∈ M14SqrtParameterInterval 0 (b ^ 2) := by
    simpa only [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hpos.le] using
      (Ioc_subset_Icc_self hs)
  rw [exponentialGram_eq_jacobi_pair hM04 hM12 E b₀ hb hpos hsC i j]
  rfl

end PoincareConjecture.M14
