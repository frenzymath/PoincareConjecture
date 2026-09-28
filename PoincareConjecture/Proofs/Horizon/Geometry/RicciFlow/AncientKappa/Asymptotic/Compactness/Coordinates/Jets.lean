import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.SpatialJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

theorem tendstoUniformlyOn_coordinate_metricJet
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S)
    (q : G.limitCarrier.carrier) (r : ℕ) (i j : Fin n)
    (K : Set (ℝ × EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hKt : ∀ p ∈ K, p.1 ∈ Ioo a b)
    (hKc : ∀ p ∈ K, p.2 ∈ (extChartAt (𝓡 n) q).target) :
    TendstoUniformlyOn (fun k ↦ iteratedFDeriv ℝ r
      (G.limitCarrier.coordinateCoefficient q
        (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k)) i j))
      (iteratedFDeriv ℝ r (G.limitCarrier.coordinateCoefficient q
        (fun t x v w ↦ G.limitCarrier.metricInner (G.limitFlow.metricAt t) x v w) i j))
      atTop K := by
  let f := fun p : ℝ × EuclideanSpace ℝ (Fin n) ↦ (extChartAt (𝓡 n) q).symm p.2
  have hf : ContinuousOn f K :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.comp
      continuous_snd.continuousOn hKc
  obtain ⟨s, hs⟩ := G.exists_exhaustion_superset (hK.image_of_continuousOn hf)
  have hdom : K ⊆ {p | p.1 ∈ Ioo a b ∧ p.2 ∈ (extChartAt (𝓡 n) q).target ∧
      (extChartAt (𝓡 n) q).symm p.2 ∈ G.exhaustion s} :=
    fun p hp ↦ ⟨hKt p hp, hKc p hp, hs (mem_image_of_mem f hp)⟩
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨N, _, hN⟩ := G.pullback_metric_CInfinity q s r K hK hdom ε hε
  filter_upwards [eventually_ge_atTop N] with k hk p hp
  simpa only [dist_eq_norm, norm_sub_rev, MetricJet] using hN k hk i j p hp

theorem tendstoUniformlyOn_coordinate_spatial_metricJet
    {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S)
    (q : G.limitCarrier.carrier) (r : ℕ) (i j : Fin n)
    (t : ℝ) (ht : t ∈ Ioo a b)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hKc : K ⊆ (extChartAt (𝓡 n) q).target) :
    TendstoUniformlyOn (fun k ↦ iteratedFDeriv ℝ r (fun y ↦
      G.limitCarrier.coordinateCoefficient q
        (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k))
        i j (t, y)))
      (iteratedFDeriv ℝ r (fun y ↦ G.limitCarrier.coordinateCoefficient q
        (fun s x v w ↦ G.limitCarrier.metricInner (G.limitFlow.metricAt s) x v w) i j (t, y)))
      atTop K := by
  let P := ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (F := ℝ) (fun _ : Fin r ↦
      ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin n)))
  let e := fun y : EuclideanSpace ℝ (Fin n) ↦ (t, y)
  have he : Continuous e := continuous_const.prodMk continuous_id
  have hfull := G.tendstoUniformlyOn_coordinate_metricJet q r i j (e '' K)
    (hK.image he) (by rintro p ⟨y, hy, rfl⟩; exact ht)
    (by rintro p ⟨y, hy, rfl⟩; exact hKc hy)
  have hrestricted := (hfull.comp e).mono (fun y hy ↦ mem_image_of_mem e hy)
  have hproject := P.uniformContinuous.comp_tendstoUniformlyOn hrestricted
  have hlim : EqOn (fun y ↦ P (iteratedFDeriv ℝ r
      (G.limitCarrier.coordinateCoefficient q
        (fun s x v w ↦ G.limitCarrier.metricInner (G.limitFlow.metricAt s) x v w)
          i j) (t, y)))
      (iteratedFDeriv ℝ r (fun y ↦ G.limitCarrier.coordinateCoefficient q
        (fun s x v w ↦ G.limitCarrier.metricInner (G.limitFlow.metricAt s) x v w)
          i j (t, y))) K := by
    intro y hy
    ext v
    exact (Poincare.Analysis.iteratedFDeriv_spatial_slice _
      (G.limitFlow.contDiffAt_coordinateCoefficient_metric q i j (t, y) ht (hKc hy)) r v).symm
  have hc : ContinuousOn (extChartAt (𝓡 n) q).symm K :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hKc
  obtain ⟨s, hs⟩ := G.exists_exhaustion_superset (hK.image_of_continuousOn hc)
  apply (hproject.congr_right hlim).congr
  filter_upwards [eventually_ge_atTop s] with k hk y hy
  ext v
  exact (Poincare.Analysis.iteratedFDeriv_spatial_slice _
    ((G.embedding k).contDiffAt_coordinateCoefficient_pullback (G.exhaustion_open k)
      q i j (t, y) ht ⟨hKc hy,
        G.exhaustion_monotone hk (hs (mem_image_of_mem _ hy))⟩) r v).symm

end PoincareConjecture.PointedGeometricConvergence
