import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Basic.Restart.LocalExtraction
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Limits.CompatibleSmoothLimits

/-!
# Metric-general The interior coefficient limit on the original cap

The common local limits assemble on the literal product of the original
cap and the open time interval. This is a coefficient limit, before the
included initial endpoint and actual metric/connection reconstruction
required by Morgan-Tian Theorem 12.5, p. 297.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M34

open SpacetimeBounds

/-- A smooth interior coefficient limit of one compact approximation
subsequence, on the original R3 (Theorem 12.5, p. 297). -/
structure MetricInteriorCoefficientLimit
    {ginit : RiemannianMetric 3 StandardCapSpace} {Mfamily : ℕ → Type}
  [∀ k, TopologicalSpace (Mfamily k)] [∀ k, ChartedSpace StandardCapSpace (Mfamily k)]
  [∀ k, IsManifold (𝓡 3) ∞ (Mfamily k)]
    (A : MetricFlowApproximation ginit Mfamily) where
  /-- The same subsequence is used in every coordinate ball. -/
  subsequence : ℕ → ℕ
  /-- The selected indices tend to infinity. -/
  strictMono : StrictMono subsequence
  /-- The actual bilinear coefficient function on the original spacetime. -/
  coefficients : ℝ × StandardCapSpace → MetricCoefficient 3
  /-- Ordinary joint smoothness is asserted only at interior times. -/
  smooth : ContDiffOn ℝ ∞ coefficients (Ioo 0 A.time ×ˢ univ)
  /-- All joint derivatives converge uniformly on each interior compact set. -/
  jet_convergence : ∀ m K, IsCompact K → K ⊆ Ioo 0 A.time ×ˢ univ →
    TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m
        (fun p : ℝ × StandardCapSpace => A.coefficients (subsequence k) p.1 p.2))
      (iteratedFDeriv ℝ m coefficients) atTop K

/-- The common local extraction constructs a smooth interior coefficient
limit on the original cap (Theorem 12.5, p. 297). -/
theorem metricInteriorCoefficientLimit_exists
    {ginit : RiemannianMetric 3 StandardCapSpace} {Mfamily : ℕ → Type}
  [∀ k, TopologicalSpace (Mfamily k)] [∀ k, ChartedSpace StandardCapSpace (Mfamily k)]
  [∀ k, IsManifold (𝓡 3) ∞ (Mfamily k)]
    (A : MetricFlowApproximation ginit Mfamily) (P : RicciFlowCurvatureTheory.{0}) :
    Nonempty (MetricInteriorCoefficientLimit A) := by
  obtain ⟨σ, hσ, F, hF, hconv⟩ := A.exists_local_interior_limits P
  have hcompact (K : Set (ℝ × StandardCapSpace)) (hK : IsCompact K)
      (hKΩ : K ⊆ Ioo 0 A.time ×ˢ univ) : ∃ i, K ⊆ A.interiorBallDomain i := by
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (f := Prod.snd)
      continuous_snd.continuousOn
    obtain ⟨i, hi⟩ := exists_nat_gt B
    refine ⟨i, ?_⟩
    intro p hp
    refine ⟨(hKΩ hp).1, ?_⟩
    simp only [Metric.mem_ball, dist_zero_right]
    linarith [hB p hp]
  have hcover (p : ℝ × StandardCapSpace) (hp : p ∈ Ioo 0 A.time ×ˢ univ) :
      ∃ i, p ∈ A.interiorBallDomain i := by
    obtain ⟨i, hi⟩ := hcompact {p} isCompact_singleton (singleton_subset_iff.mpr hp)
    exact ⟨i, hi (mem_singleton p)⟩
  obtain ⟨G, hG, hGconv⟩ := exists_contDiffOn_limit_of_open_exhaustion
    (Ω := Ioo 0 A.time ×ˢ (univ : Set StandardCapSpace))
    (A.interiorBallDomain_isOpen) (fun _ _ hp => ⟨hp.1, mem_univ _⟩)
    hcover hcompact hF hconv
  exact ⟨{
    subsequence := σ
    strictMono := hσ
    coefficients := G
    smooth := hG
    jet_convergence := hGconv }⟩

end PoincareMT.M34
