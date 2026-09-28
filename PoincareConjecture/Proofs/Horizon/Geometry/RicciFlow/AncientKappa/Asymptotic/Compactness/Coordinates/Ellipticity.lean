import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.Coefficients
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.CompactEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

theorem eventually_uniformEllipticity_pulledChartCoefficients
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (q : G.limitCarrier.carrier)
    (t : ℝ) (ht : t ∈ Ioo a b) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K) (hKc : K ⊆ (extChartAt (𝓡 n) q).target) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop, ∀ y ∈ K, ∀ v,
      c * ‖v‖ ^ 2 ≤ G.pulledChartCoefficients q k t y v v := by
  let g := G.limitFlow.metricAt t
  let c := (extChartAt (𝓡 n) q).symm
  have hpos : ∀ y ∈ K, ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 →
      0 < g.pullbackCoefficients c y v v := by
    intro y hy v hv
    have hi : (mfderiv (𝓡 n) (𝓡 n) c y).IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 n) (hKc hy)
    apply g.pos
    intro hzero
    apply hv
    apply hi.injective
    rw [map_zero]
    exact hzero
  obtain ⟨d, hd, hlow⟩ := exists_uniform_bilinear_lower_bound hK
    ((g.contDiffOn_chartCoefficients q).continuousOn.mono hKc) hpos
  have hc : ContinuousOn c K :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hKc
  have himage := hK.image_of_continuousOn hc
  obtain ⟨s, hs⟩ := G.exists_exhaustion_superset himage
  refine ⟨d / 2, by positivity, ?_⟩
  filter_upwards [G.eventually_pullback_inner_bounds himage ht
    (by norm_num : (0 : ℝ) < 1 / 2), eventually_ge_atTop s] with k hk hsk y hy v
  have hys := G.exhaustion_monotone hsk (hs (mem_image_of_mem c hy))
  rw [G.pulledChartCoefficients_eq q k t ht (hKc hy) hys]
  have hb := (hk (c y) (mem_image_of_mem c hy) (mfderiv (𝓡 n) (𝓡 n) c y v)).1
  have hl := hlow y hy v
  change d * ‖v‖ ^ 2 ≤ g.inner (c y) (mfderiv (𝓡 n) (𝓡 n) c y v)
    (mfderiv (𝓡 n) (𝓡 n) c y v) at hl
  change (1 - (1 : ℝ) / 2) * g.inner (c y) (mfderiv (𝓡 n) (𝓡 n) c y v)
    (mfderiv (𝓡 n) (𝓡 n) c y v) ≤ _ at hb
  nlinarith

end PoincareConjecture.PointedGeometricConvergence
