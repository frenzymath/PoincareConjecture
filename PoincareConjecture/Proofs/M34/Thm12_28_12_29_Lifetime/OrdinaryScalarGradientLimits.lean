import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.OrdinarySpatialJets
import PoincareConjecture.Proofs.M34.Standard.CoordinateScalarGradient
import PoincareConjecture.Proofs.M34.Standard.ScalarAnalyticConvergence
import PoincareConjecture.Proofs.M34.Standard.MetricJetConvergence
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Convergence.LocalRealization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M34

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "G" => ordinaryChapter11Flow (I := I) (F := F) R

theorem ordinaryChapter11_tendsto_scalarGradient_zero
    (p : ℕ → (G).point) (hpositive : ∀ k, 0 < (G).scalar (p k))
    (hdiverges : Tendsto (fun k => (G).scalar (p k)) atTop atTop) {J : Set ℝ}
    (C : GeneralizedBlowupConvergence
      (fixedFlowBlowupSequence (G) p hpositive hdiverges) J)
    (hJ : UniqueDiffOn ℝ J) (x : C.limit.sliceCarrier.carrier) :
    letI := C.limit.carrier.topologicalSpace
    letI := C.limit.carrier.chartedSpace
    letI := C.limit.carrier.isManifold
    let h0 : ∀ k, 0 ∈ Icc (-C.exhaustion.time k) 0 :=
      fun k => ⟨neg_nonpos.mpr (C.exhaustion.time_pos k).le, le_rfl⟩
    Tendsto (fun k =>
      let z := (C.embedding k).pointMap 0 (h0 k) x
      scalarGradientNorm ((G).metric z.1) ((G).connection z.1) z.2 /
        ((G).scalar (p (C.subsequence k))) ^ (3 / 2 : ℝ)) atTop
      (𝓝 (scalarGradientNorm (C.limit.flow.metric 0) (C.limit.flow.connection 0) x)) := by
  classical
  let := C.limit.carrier.topologicalSpace
  let := C.limit.carrier.chartedSpace
  let := C.limit.carrier.isManifold
  let h0 : ∀ k, 0 ∈ Icc (-C.exhaustion.time k) 0 :=
    fun k => ⟨neg_nonpos.mpr (C.exhaustion.time_pos k).le, le_rfl⟩
  let c := extChartAt (𝓡 3) x
  let z := c x
  have hz : z ∈ c.target := c.map_source (mem_extChartAt_source x)
  have hcx : (extChartAt (𝓡 3) x).symm z = x := c.left_inv (mem_extChartAt_source x)
  obtain ⟨g, D, V, hVo, hzV, _, heq⟩ := C.limit.carrier.exists_local_coordinate_realization
    (C.limit.flow.metric 0) x 0 z hz
  have hg : ∀ᶠ y in 𝓝 z, ∀ a b : Fin 3,
      g.euclideanCoefficients y (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b) =
      C.limit.carrier.coordinateCoefficient x
        (fun _ y v w => (C.limit.flow.metric 0).inner y v w) a b (0, y) :=
    Filter.Eventually.mono (hVo.mem_nhds hzV) heq
  obtain ⟨j, hj⟩ := C.exists_exhaustion_superset (isCompact_singleton (x := x))
  have hcaptured {k : ℕ} (hk : j ≤ k) : c.symm z ∈ C.exhaustion.space k := by
    rw [hcx]
    exact C.exhaustion.space_increasing hk (hj (mem_singleton _))
  have hreal : ∀ᶠ k : ℕ in atTop,
      ∃ gd : Σ g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)), LeviCivitaData g,
        ∀ᶠ y in 𝓝 z, ∀ a b : Fin 3,
          gd.1.euclideanCoefficients y (EuclideanSpace.basisFun (Fin 3) ℝ a)
            (EuclideanSpace.basisFun (Fin 3) ℝ b) =
          blowupPullbackCoefficient (C.embedding k) x a b (0, y) := by
    filter_upwards [eventually_ge_atTop j] with k hk
    obtain ⟨gk, Dk, Vk, hVko, hzVk, _, heqk⟩ :=
      (C.embedding k).exists_local_coordinate_realization (C.exhaustion.space_open k)
        x (h0 k) z ⟨hz, hcaptured hk⟩
    exact ⟨⟨gk, Dk⟩, Filter.Eventually.mono (hVko.mem_nhds hzVk) heqk⟩
  obtain ⟨gd, hgd⟩ := hreal.choice
  have hjets (r : ℕ) (a b : Fin 3) :
      Tendsto (fun k => iteratedFDeriv ℝ r
        (fun y => (gd k).1.inner y (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)) z) atTop
        (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) z)) := by
    erw [C.limit.carrier.iteratedFDeriv_coordinateCoefficient_eq_of_eventuallyEq
      x _ 0 z g hg r a b]
    apply (ordinaryChapter11_tendsto_spatial_metricJet R p hpositive hdiverges C
      hJ x r a b (0, z) ⟨C.limit.zero_mem, hz⟩).congr'
    filter_upwards [hgd] with k hk
    have he : (fun y => (gd k).1.inner y (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) =ᶠ[𝓝 z]
        (fun y => blowupPullbackCoefficient (C.embedding k) x a b (0, y)) :=
      hk.mono (fun y hy => hy a b)
    exact (he.iteratedFDeriv ℝ r).self_of_nhds.symm
  have hn := LeviCivitaData.tendsto_scalarGradient_tangentNorm_of_metric_jets
    (fun k => (gd k).2) D z (fun r _ =>
      RiemannianMetric.tendsto_iteratedFDeriv_euclideanCoefficients_of_scalar_jets
        r z (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (hjets r))
  have hlimit : g.tangentNorm z (D.gradient D.scalarCurvature z) =
      scalarGradientNorm (C.limit.flow.metric 0) (C.limit.flow.connection 0) x := by
    rw [← scalarGradientNorm_eq_tangentNorm]
    simpa only [hcx] using C.limit.carrier.scalarGradientNorm_eq_of_coordinate_germ
      (C.limit.flow.metric 0) (C.limit.flow.connection 0) x 0 z hz g D hg
  rw [hlimit] at hn
  apply hn.congr'
  filter_upwards [hgd, eventually_ge_atTop j] with k hk hjk
  rw [← scalarGradientNorm_eq_tangentNorm]
  let A : (G).point → ℝ := fun y =>
    scalarGradientNorm ((G).metric y.1) ((G).connection y.1) y.2
  have ha := (C.embedding k).scalarGradientNorm_eq_of_coordinate_germ
    (C.exhaustion.space_open k) x (h0 k) z ⟨hz, hcaptured hjk⟩ (gd k).1 (gd k).2 hk
  change scalarGradientNorm (gd k).1 (gd k).2 z =
    A ((C.embedding k).pointMap 0 (h0 k) ((extChartAt (𝓡 3) x).symm z)) /
      ((G).scalar (p (C.subsequence k))) ^ (3 / 2 : ℝ) at ha
  rw [hcx] at ha
  exact ha

end PoincareConjecture.M34
