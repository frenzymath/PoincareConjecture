import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.ScalarConvergence










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M28

open SpacetimeBounds Poincare.Analysis.Calculus




theorem tendstoUniformlyOn_metricTwoJet_of_uniform_bilinear_jets
    {n : ℕ} {B : ℕ → EuclideanSpace ℝ (Fin n) → MetricCoefficient n}
    {B0 : EuclideanSpace ℝ (Fin n) → MetricCoefficient n}
    {K : Set (EuclideanSpace ℝ (Fin n))}
    (h : ∀ m ≤ 2, TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (B k))
      (iteratedFDeriv ℝ m B0) atTop K) :
    TendstoUniformlyOn (fun k => metricTwoJet (B k)) (metricTwoJet B0) atTop K := by
  have h0 := (ContinuousMultilinearMap.uniformContinuous_eval_const
    (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn (h 0 (by omega))
  have h1 := (ContinuousMultilinearMap.uniformContinuous_eval_const
    (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn
      (tendstoUniformlyOn_fderiv_jets 0 (h 1 (by omega)))
  have h2 := (ContinuousMultilinearMap.uniformContinuous_eval_const
    (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn
      (tendstoUniformlyOn_fderiv_jets 0
        (tendstoUniformlyOn_fderiv_jets 1 (h 2 (by omega))))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro delta hdelta
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp h0 delta hdelta,
    Metric.tendstoUniformlyOn_iff.mp h1 delta hdelta,
    Metric.tendstoUniformlyOn_iff.mp h2 delta hdelta] with k hk0 hk1 hk2
  intro x hx
  exact max_lt (hk0 x hx) (max_lt (hk1 x hx) (hk2 x hx))




theorem tendstoUniformlyOn_jetScalarCurvature_of_metricTwoJet
    {B : ℕ → EuclideanSpace ℝ (Fin 3) → MetricCoefficient 3}
    {B0 : EuclideanSpace ℝ (Fin 3) → MetricCoefficient 3}
    {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) (hcontinuous : ContinuousOn (metricTwoJet B0) K)
    (hinvertible : ∀ x ∈ K, (B0 x).IsInvertible)
    (hjets : TendstoUniformlyOn (fun k => metricTwoJet (B k))
      (metricTwoJet B0) atTop K) :
    TendstoUniformlyOn (fun k x => tube.jetScalarCurvature (metricTwoJet (B k) x))
      (fun x => tube.jetScalarCurvature (metricTwoJet B0 x)) atTop K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro delta hdelta
  have hcompact : IsCompact (metricTwoJet B0 '' K) := hK.image_of_continuousOn hcontinuous
  obtain ⟨eta, heta, hmodulus⟩ := tube.exists_jetScalarCurvature_uniform_modulus hcompact
    (by rintro _ ⟨x, hx, rfl⟩; exact hinvertible x hx) hdelta
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hjets eta heta] with k hk
  intro x hx
  have hdist : dist (metricTwoJet (B k) x) (metricTwoJet B0 x) < eta := by
    simpa only [dist_comm] using hk x hx
  simpa only [Real.dist_eq, abs_sub_comm] using
    hmodulus (metricTwoJet B0 x) (mem_image_of_mem _ hx) (metricTwoJet (B k) x) hdist

end PoincareConjecture.M28
