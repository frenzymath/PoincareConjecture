import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Coordinates.Coefficients
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Poincare.Analysis.Calculus
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

theorem coordinate_spatial_metricJet_bounded
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (q : G.limitCarrier.carrier)
    (t : ℝ) (ht : t ∈ Ioo a b) (m : ℕ) (i j : Fin n)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hKc : K ⊆ (extChartAt (𝓡 n) q).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop, ∀ y ∈ K,
      ‖iteratedFDeriv ℝ m (fun z ↦ G.limitCarrier.coordinateCoefficient q
        (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k))
          i j (t, z)) y‖ ≤ C := by
  let A := fun y ↦ G.limitCarrier.coordinateCoefficient q
    (fun s x v w ↦ G.limitCarrier.metricInner (G.limitFlow.metricAt s) x v w) i j (t, y)
  have hA : ContinuousOn (iteratedFDeriv ℝ m A) K := by
    intro y hy
    apply ContinuousAt.continuousWithinAt
    exact (G.limitCarrier.contDiffAt_coordinateCoefficient_metric (G.limitFlow.metricAt t)
      q i j t y (hKc hy)).continuousAt_iteratedFDeriv
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl m)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hA
  refine ⟨max B 0 + 1, by positivity, ?_⟩
  have hc := Metric.tendstoUniformlyOn_iff.mp
    (G.tendstoUniformlyOn_coordinate_spatial_metricJet q m i j t ht K hK hKc) 1 zero_lt_one
  filter_upwards [hc] with k hk y hy
  have hh := hk y hy
  rw [dist_eq_norm, norm_sub_rev] at hh
  calc
    _ ≤ ‖iteratedFDeriv ℝ m A y‖ + ‖iteratedFDeriv ℝ m
        (fun z ↦ G.limitCarrier.coordinateCoefficient q
          (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k)) i j (t, z)) y -
        iteratedFDeriv ℝ m A y‖ := norm_le_insert' _ _
    _ ≤ B + 1 := add_le_add (hB y hy) hh.le
    _ ≤ max B 0 + 1 := by linarith [le_max_left B 0]

theorem locallyEventuallyBoundedDerivatives_pulledChartCoefficients
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (q : G.limitCarrier.carrier)
    (t : ℝ) (ht : t ∈ Ioo a b) :
    LocallyEventuallyBoundedDerivatives (extChartAt (𝓡 n) q).target
      (fun k ↦ G.pulledChartCoefficients q k t) := by
  intro K hK hKc m
  choose B hB hbound using fun i j ↦
    G.coordinate_spatial_metricJet_bounded q t ht m i j K hK hKc
  let C := ∑ i : Fin n, ∑ j : Fin n, B i j
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hB i j
  have hBC (i j : Fin n) : B i j ≤ C :=
    (Finset.single_le_sum (fun j _ ↦ hB i j) (Finset.mem_univ j)).trans
      (Finset.single_le_sum
        (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hB i j) (Finset.mem_univ i))
  have hc : ContinuousOn (extChartAt (𝓡 n) q).symm K :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hKc
  obtain ⟨s, hs⟩ := G.exists_exhaustion_superset (hK.image_of_continuousOn hc)
  refine ⟨(n : ℝ) ^ 2 * C, ?_⟩
  filter_upwards [eventually_ge_atTop s,
    eventually_all.mpr (fun i ↦ eventually_all.mpr (hbound i))] with k hk hb y hy
  have hys := G.exhaustion_monotone hk (hs (mem_image_of_mem _ hy))
  apply norm_iteratedFDeriv_bilinear_le_of_entries
    (G.contDiffAt_pulledChartCoefficients q k t ht (hKc hy) hys) m hC
  intro i j
  have hnear :
      (fun z ↦ G.pulledChartCoefficients q k t z (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j)) =ᶠ[𝓝 y]
      (fun z ↦ G.limitCarrier.coordinateCoefficient q
        (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k)) i j (t, z)) := by
    have hsmooth := (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.continuousAt
      ((isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds (hKc hy))
    filter_upwards [(isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds (hKc hy),
      hsmooth.preimage_mem_nhds ((G.exhaustion_open k).mem_nhds hys)] with z hzc hzs
    exact G.pulledChartCoefficients_basis_eq q k t ht hzc hzs i j
  rw [(hnear.iteratedFDeriv ℝ m).self_of_nhds]
  exact (hb i j y hy).trans (hBC i j)

end PoincareConjecture.PointedGeometricConvergence
