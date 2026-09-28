import PoincareConjecture.Proofs.M47.TerminalCurvatureChartScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalCurvature_eventually_actual_scalar_error
    {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)] [∀ k, ChartedSpace E (M k)]
    [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, T2Space (M k)]
    {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X] [T2Space X]
    {g : ∀ k, RiemannianMetric 3 (M k)} (D : ∀ k, LeviCivitaData (g k))
    {h : RiemannianMetric 3 X} (D0 : LeviCivitaData h)
    (f : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) E (M k) ∞)
    (f0 : PartialDiffeomorph (𝓡 3) (𝓡 3) E X ∞)
    {K : Set E} (hK : IsCompact K) (hK0 : K ⊆ f0.source)
    (hsource : ∀ᶠ k in atTop, K ⊆ (f k).source)
    (hjet : ∀ j ≤ 2, TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ j ((g k).pullbackCoefficients (f k)))
      (iteratedFDeriv ℝ j (h.pullbackCoefficients f0)) atTop K)
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ k in atTop, ∀ x ∈ K,
      |(D k).scalarCurvature (f k x) - D0.scalarCurvature (f0 x)| < eta := by
  have hB0 : ContDiffOn ℝ ∞ (h.pullbackCoefficients f0) f0.source := by
    intro x hx
    exact (h.contDiffAt_pullbackCoefficients
      (f0.contMDiffOn_toFun.contMDiffAt (f0.open_source.mem_nhds hx))).contDiffWithinAt
  have hinv : ∀ x ∈ f0.source, (h.pullbackCoefficients f0 x).IsInvertible := by
    intro x hx
    have hlocal := f0.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ hx
    exact h.isInvertible_pullbackCoefficients
      (hlocal.mfderivToContinuousLinearEquiv (by simp)).injective
  filter_upwards [hsource,
    terminalCurvature_eventually_uniform_scalar_jet_error f0.open_source hK hK0 hB0 hinv
      hjet heta] with k hk hs x hx
  have hread := hs x hx
  rw [terminalCurvature_partial_chart_scalar (D k) (f k) (hk hx),
    terminalCurvature_partial_chart_scalar D0 f0 (hK0 hx)] at hread
  exact hread

end PoincareConjecture.M47
