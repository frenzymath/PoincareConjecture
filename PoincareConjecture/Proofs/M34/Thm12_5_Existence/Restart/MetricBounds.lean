import PoincareConjecture.Proofs.M34.Thm12_5_Existence.Restart.Convergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34.MetricInteriorCoefficientLimit

variable {ginit : RiemannianMetric 3 StandardCapSpace} {Mfamily : ℕ → Type}
  [∀ k, TopologicalSpace (Mfamily k)] [∀ k, ChartedSpace StandardCapSpace (Mfamily k)]
  [∀ k, IsManifold (𝓡 3) ∞ (Mfamily k)]
  {A : MetricFlowApproximation ginit Mfamily}
  (G : MetricInteriorCoefficientLimit A)

theorem coefficients_apply_tendsto {t : ℝ} (ht : t ∈ Ioo 0 A.time)
    (x u v : StandardCapSpace) :
    Tendsto (fun k => A.coefficients (G.subsequence k) t x u v) atTop
      (𝓝 (G.coefficients (t, x) u v)) := by
  have hc : Continuous (fun B : SpacetimeBounds.MetricCoefficient 3 => B u v) := by
    fun_prop
  exact hc.continuousAt.tendsto.comp (G.coefficients_tendsto ht x)

theorem coefficients_symm {t : ℝ} (ht : t ∈ Ioo 0 A.time) (x u v : StandardCapSpace) :
    G.coefficients (t, x) u v = G.coefficients (t, x) v u := by
  apply tendsto_nhds_unique (G.coefficients_apply_tendsto ht x u v)
  apply (G.coefficients_apply_tendsto ht x v u).congr'
  exact Eventually.of_forall (fun k => ((A.flow (G.subsequence k)).metric t).symm _ _ _)

theorem coefficients_exp_bounds (P : RicciFlowCurvatureTheory.{0})
    {t : ℝ} (ht : t ∈ Ioo 0 A.time) (x v : StandardCapSpace) :
    Real.exp (-6 * A.curvature_bound 0 * t) * ginit.euclideanCoefficients x v v ≤
        G.coefficients (t, x) v v ∧
      G.coefficients (t, x) v v ≤
        Real.exp (6 * A.curvature_bound 0 * t) * ginit.euclideanCoefficients x v v := by
  have hs := G.strictMono.tendsto_atTop.eventually
    (A.compact_sources _ (isCompact_singleton (x := x)))
  have hb : ∀ᶠ k : ℕ in atTop,
      Real.exp (-6 * A.curvature_bound 0 * t) * ginit.euclideanCoefficients x v v ≤
          A.coefficients (G.subsequence k) t x v v ∧
        A.coefficients (G.subsequence k) t x v v ≤
          Real.exp (6 * A.curvature_bound 0 * t) * ginit.euclideanCoefficients x v v := by
    filter_upwards [hs] with k hk
    exact A.coefficients_exp_bounds P (G.subsequence k) (Ioo_subset_Icc_self ht)
      (hk (mem_singleton x)) v
  exact ⟨ge_of_tendsto (G.coefficients_apply_tendsto ht x v v) (hb.mono fun _ h => h.1),
    le_of_tendsto (G.coefficients_apply_tendsto ht x v v) (hb.mono fun _ h => h.2)⟩

theorem coefficients_pos (P : RicciFlowCurvatureTheory.{0})
    {t : ℝ} (ht : t ∈ Ioo 0 A.time) (x v : StandardCapSpace) (hv : v ≠ 0) :
    0 < G.coefficients (t, x) v v :=
  (mul_pos (Real.exp_pos _) (ginit.pos x v hv)).trans_le
    (G.coefficients_exp_bounds P ht x v).1

end PoincareConjecture.M34.MetricInteriorCoefficientLimit
