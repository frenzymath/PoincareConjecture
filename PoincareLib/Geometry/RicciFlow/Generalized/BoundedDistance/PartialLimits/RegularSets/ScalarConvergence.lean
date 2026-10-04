import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.RegularSets.MetricConvergence
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Spheres.RoundTransfer
import PoincareLib.Analysis.Calculus.SmoothCompactness.Pullback

/-!
# Scalar curvature on the actual regular spatial embeddings

The metric jets retained by Theorem 5.6 determine scalar curvature at each
fixed limit point. Source maps are used only on their eventual open
exhaustion domains. Morgan--Tian, pp. 85-87 and 254-255; M28 derivation 72.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M28

open SpacetimeBounds Poincare.Analysis.Calculus

private theorem tendsto_values_of_uniform_zero_jets
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {B : ℕ → E → F} {B₀ : E → F} {K : Set E} {x : E}
    (h : TendstoUniformlyOn (fun k => iteratedFDeriv ℝ 0 (B k))
      (iteratedFDeriv ℝ 0 B₀) atTop K) (hx : x ∈ K) :
    Tendsto (fun k => B k x) atTop (𝓝 (B₀ x)) := by
  exact ((ContinuousMultilinearMap.uniformContinuous_eval_const
    (0 : Fin 0 → E)).comp_tendstoUniformlyOn h).tendsto_at hx

/-- Derivatives through order two give the coordinate metric two-jet
limit, with the actual Fréchet derivatives (M28 derivation 72). -/
theorem tendsto_metricTwoJet_of_uniform_bilinear_jets
    {n : ℕ} {B : ℕ → EuclideanSpace ℝ (Fin n) → MetricCoefficient n}
    {B₀ : EuclideanSpace ℝ (Fin n) → MetricCoefficient n}
    {K : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}
    (h : ∀ m ≤ 2, TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (B k))
      (iteratedFDeriv ℝ m B₀) atTop K) (hx : x ∈ K) :
    Tendsto (fun k => metricTwoJet (B k) x) atTop (𝓝 (metricTwoJet B₀ x)) := by
  have h₀ := tendsto_values_of_uniform_zero_jets (h 0 (by omega)) hx
  have h₁ := tendsto_values_of_uniform_zero_jets
    (tendstoUniformlyOn_fderiv_jets 0 (h 1 (by omega))) hx
  have h₂ := tendsto_values_of_uniform_zero_jets
    (tendstoUniformlyOn_fderiv_jets 0
      (tendstoUniformlyOn_fderiv_jets 1 (h 2 (by omega)))) hx
  exact h₀.prodMk_nhds (h₁.prodMk_nhds h₂)

namespace RegularPointedMetricConvergence

variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)]
  {g : ∀ k, RiemannianMetric 3 (M k)} {p : ∀ k, M k}

/-- The scalar at a fixed limit point is the limit of the actual source
scalars under the retained embeddings. No scalar convergence is assumed
(Theorem 5.6, pp. 85-87; Claims 10.10-10.11, pp. 254-255; derivation 72). -/
theorem tendsto_scalarCurvature
    (G : RegularPointedMetricConvergence g p) (D : ∀ k, LeviCivitaData (g k)) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (D₀ : LeviCivitaData G.limitMetric) (q : G.limitCarrier.carrier),
      Tendsto (fun k => (D (G.subsequence k)).scalarCurvature (G.embedding k q))
        atTop (𝓝 (D₀.scalarCurvature q)) := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D₀ q
  let c := extChartAt (𝓡 3) q
  let x := c q
  have hx : x ∈ c.target := mem_extChartAt_target q
  have hc : c.symm x = q := extChartAt_to_inv q
  have hjets := tendsto_metricTwoJet_of_uniform_bilinear_jets
    (fun m _ => G.metric_jets q m {x} (isCompact_singleton)
      (singleton_subset_iff.mpr hx)) (mem_singleton x)
  have hread := (tube.contDiffAt_jetScalarCurvature
    (J := metricTwoJet (G.limitMetric.pullbackCoefficients c.symm) x)
    (G.limitMetric.isInvertible_chartCoefficients q hx)).continuousAt.tendsto.comp hjets
  have hlimit : tube.jetScalarCurvature
      (metricTwoJet (G.limitMetric.pullbackCoefficients c.symm) x) =
      D₀.scalarCurvature q := by
    rw [tube.jetScalarCurvature_metricTwoJet_pullback D₀
      (isOpen_extChartAt_target q) (contMDiffOn_extChartAt_symm q)
      (fun y hy => by
        simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
          isInvertible_mfderivWithin_extChartAt_symm hy) hx, hc]
  rw [hlimit] at hread
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ
    (fun j => subset_closure.trans (G.exhaustion_step j))
  obtain ⟨j, hj⟩ : ∃ j, q ∈ G.exhaustion j := by
    have hq : q ∈ ⋃ j, G.exhaustion j := G.exhaustion_covers.symm ▸ mem_univ q
    exact mem_iUnion.mp hq
  apply hread.congr'
  filter_upwards [eventually_ge_atTop j] with k hk
  let U := c.target ∩ c.symm ⁻¹' G.exhaustion k
  have hU : IsOpen U :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.isOpen_inter_preimage
      (isOpen_extChartAt_target q) (G.exhaustion_open k)
  have hxU : x ∈ U := ⟨hx, by simpa only [mem_preimage, hc] using hmono hk hj⟩
  have hchart (y) (hy : y ∈ U) : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm y :=
    (contMDiffOn_extChartAt_symm q).contMDiffAt
      ((isOpen_extChartAt_target q).mem_nhds hy.1)
  have hmap (y) (hy : y ∈ U) :
      IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (G.embedding k) (c.symm y) :=
    G.embedding_smooth k ⟨c.symm y, hy.2⟩
  have hsmooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (G.embedding k ∘ c.symm) U :=
    fun y hy => ((hmap y hy).contMDiffAt.comp y (hchart y hy)).contMDiffWithinAt
  have hinvertible (y) (hy : y ∈ U) :
      (mfderiv (𝓡 3) (𝓡 3) (G.embedding k ∘ c.symm) y).IsInvertible := by
    rw [mfderiv_comp y ((hmap y hy).mdifferentiableAt (by simp))
      ((hchart y hy).mdifferentiableAt (by simp))]
    have hi : (mfderiv (𝓡 3) (𝓡 3) c.symm y).IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm hy.1
    exact (show (mfderiv (𝓡 3) (𝓡 3) (G.embedding k) (c.symm y)).IsInvertible from
      ⟨(hmap y hy).mfderivToContinuousLinearEquiv (by simp), rfl⟩).comp hi
  simpa only [Function.comp_apply, hc] using
    tube.jetScalarCurvature_metricTwoJet_pullback (D (G.subsequence k))
      hU hsmooth hinvertible hxU

/-- A uniform eventual source scalar lower bound survives on the first
spatial limit (Claims 10.10-10.11, pp. 254-255; derivation 72). -/
theorem scalarCurvature_lower_bound
    (G : RegularPointedMetricConvergence g p) (D : ∀ k, LeviCivitaData (g k)) :
    letI := G.limitCarrier.topologicalSpace
    letI := G.limitCarrier.chartedSpace
    letI := G.limitCarrier.isManifold
    ∀ (D₀ : LeviCivitaData G.limitMetric) (q : G.limitCarrier.carrier) (b : ℝ),
      (∀ᶠ k in atTop, b ≤ (D (G.subsequence k)).scalarCurvature (G.embedding k q)) →
      b ≤ D₀.scalarCurvature q := by
  let := G.limitCarrier.topologicalSpace
  let := G.limitCarrier.chartedSpace
  let := G.limitCarrier.isManifold
  intro D₀ q b hb
  exact ge_of_tendsto (G.tendsto_scalarCurvature D D₀ q) hb

end RegularPointedMetricConvergence

end PoincareMT.M28
