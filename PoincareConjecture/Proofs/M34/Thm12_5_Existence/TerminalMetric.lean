import PoincareConjecture.Proofs.M34.Thm12_5_Existence.TerminalJets
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34.PartialFlowTerminalJets

open SpacetimeBounds

variable {g0 : StandardInitialMetric} {F : PartialStandardCapFlow g0} {S : ℝ}
  (L : PartialFlowTerminalJets F S)

theorem coefficients_tendsto (x : StandardCapSpace) :
    Tendsto (fun t => (F.flow.metric t).euclideanCoefficients x)
      (𝓝[<] S) (𝓝 (L.coefficients x)) := by
  let e := (continuousMultilinearCurryFin0 ℝ StandardCapSpace (MetricCoefficient 3))
  have h := e.continuous.continuousAt.tendsto.comp (L.jet_tendsto 0 x)
  convert! h using 1

theorem coefficients_apply_tendsto (x u v : StandardCapSpace) :
    Tendsto (fun t => (F.flow.metric t).inner x u v)
      (𝓝[<] S) (𝓝 (L.coefficients x u v)) := by
  have hc : Continuous (fun A : MetricCoefficient 3 => A u v) := by fun_prop
  exact hc.continuousAt.tendsto.comp (L.coefficients_tendsto x)

theorem coefficients_symm (x u v : StandardCapSpace) :
    L.coefficients x u v = L.coefficients x v u := by
  apply tendsto_nhds_unique (L.coefficients_apply_tendsto x u v)
  apply (L.coefficients_apply_tendsto x v u).congr'
  exact Eventually.of_forall (fun t => (F.flow.metric t).symm _ _ _)

variable (P : RicciFlowCurvatureTheory.{0}) (E0 : StandardCapEstimate g0)
  {B : ℝ} (hS : 0 < S) (hSF : S ≤ F.lifetime) (hB : 0 < B)
  (hfull : ∀ t ∈ Ico 0 S, ∀ x : StandardCapSpace,
    (F.flow.connection t).curvatureTensorNorm x ≤ B)

include P hS hSF hB hfull

theorem coefficients_exp_bounds (x v : StandardCapSpace) :
    Real.exp (-6 * B * S) * g0.metric.inner x v v ≤ L.coefficients x v v ∧
      L.coefficients x v v ≤ Real.exp (6 * B * S) * g0.metric.inner x v v := by
  have hm : Continuous (fun t : ℝ => Real.exp (-6 * B * t) * g0.metric.inner x v v) := by
    fun_prop
  have hp : Continuous (fun t : ℝ => Real.exp (6 * B * t) * g0.metric.inner x v v) := by
    fun_prop
  have hb : ∀ᶠ t in 𝓝[<] S,
      Real.exp (-6 * B * t) * g0.metric.inner x v v ≤ (F.flow.metric t).inner x v v ∧
        (F.flow.metric t).inner x v v ≤ Real.exp (6 * B * t) * g0.metric.inner x v v := by
    filter_upwards [Ico_mem_nhdsLT hS] with t ht
    exact partialFlow_exp_bounds F P ⟨ht.1, ht.2.trans_le hSF⟩ hB.le
      (fun s hs y => hfull s ⟨hs.1, hs.2.trans_lt ht.2⟩ y) x v
  exact ⟨le_of_tendsto_of_tendsto
      (hm.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (L.coefficients_apply_tendsto x v v) (hb.mono fun _ ht => ht.1),
    le_of_tendsto_of_tendsto (L.coefficients_apply_tendsto x v v)
      (hp.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) (hb.mono fun _ ht => ht.2)⟩

theorem coefficients_pos (x v : StandardCapSpace) (hv : v ≠ 0) :
    0 < L.coefficients x v v :=
  (mul_pos (Real.exp_pos _) (g0.metric.pos x v hv)).trans_le
    (L.coefficients_exp_bounds P hS hSF hB hfull x v).1

noncomputable def metric : RiemannianMetric 3 StandardCapSpace :=
  RiemannianMetric.ofEuclideanCoefficients L.coefficients
    (L.contDiff_coefficients P E0 hS hSF hB hfull) L.coefficients_symm
    (L.coefficients_pos P hS hSF hB hfull)

theorem metric_coefficients :
    (L.metric P E0 hS hSF hB hfull).euclideanCoefficients = L.coefficients := rfl

theorem initial_tangentNorm_le (x v : StandardCapSpace) :
    g0.metric.tangentNorm x v ≤
      Real.exp (3 * B * S) * (L.metric P E0 hS hSF hB hfull).tangentNorm x v := by
  have h := mul_le_mul_of_nonneg_left
    (L.coefficients_exp_bounds P hS hSF hB hfull x v).1 (Real.exp_nonneg (6 * B * S))
  have hcancel : Real.exp (6 * B * S) * Real.exp (-6 * B * S) = 1 := by
    rw [← Real.exp_add, show 6 * B * S + -6 * B * S = 0 by ring, Real.exp_zero]
  have hmetric : g0.metric.inner x v v ≤
      Real.exp (6 * B * S) * (L.metric P E0 hS hSF hB hfull).inner x v v := by
    change g0.metric.inner x v v ≤ Real.exp (6 * B * S) * L.coefficients x v v
    simpa only [← mul_assoc, hcancel, one_mul] using h
  have hexp : Real.exp (6 * B * S) = Real.exp (3 * B * S) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hsqrt := Real.sqrt_le_sqrt hmetric
  rw [hexp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.exp_nonneg _)] at hsqrt
  exact hsqrt

theorem metric_complete : MetricComplete (L.metric P E0 hS hSF hB hfull) :=
  RiemannianMetric.metricComplete_of_tangentNorm_comparison
    g0.metric (L.metric P E0 hS hSF hB hfull) 0 g0.complete (Real.exp_pos _)
    (L.initial_tangentNorm_le P E0 hS hSF hB hfull)

end PoincareConjecture.M34.PartialFlowTerminalJets
