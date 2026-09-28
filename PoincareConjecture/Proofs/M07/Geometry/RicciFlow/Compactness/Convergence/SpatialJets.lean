import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Convergence.MetricJets
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Convergence.CoordinateRegularity
import PoincareConjecture.Proofs.M07.Analysis.Calculus.SpatialJets
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false
open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.PointedGeometricConvergence

variable {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}

theorem eventually_contDiffAt_coordinateCoefficient
    (G : PointedGeometricConvergence S)
    (q : G.limitCarrier.carrier) (p : ℝ × EuclideanSpace ℝ (Fin n))
    (ht : p.1 ∈ Ioo T' T)
    (hp :
      letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
        G.limitCarrier.chartedSpace
      p.2 ∈ (extChartAt (𝓡 n) q).target) :
    ∀ᶠ k : ℕ in atTop, ∀ a b : Fin n,
      ContDiffAt ℝ ∞ (G.limitCarrier.coordinateCoefficient q
        (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k)) a b) p := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
    (isCompact_singleton (x := (extChartAt (𝓡 n) q).symm p.2))
  filter_upwards [eventually_ge_atTop j] with k hk a b
  exact (G.embedding k).contDiffAt_coordinateCoefficient_pullback (G.exhaustion_open k)
    q a b p ht ⟨hp, G.exhaustion_monotone hk (hj (mem_singleton _))⟩

theorem tendsto_coordinate_spatial_metricJet (G : PointedGeometricConvergence S)
    (q : G.limitCarrier.carrier) (r : ℕ) (a b : Fin n)
    (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : p.1 ∈ Ioo T' T)
    (hp :
      letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
        G.limitCarrier.chartedSpace
      p.2 ∈ (extChartAt (𝓡 n) q).target) :
    Tendsto (fun k => iteratedFDeriv ℝ r (fun y =>
      G.limitCarrier.coordinateCoefficient q
        (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k))
          a b (p.1, y)) p.2) atTop
      (𝓝 (iteratedFDeriv ℝ r (fun y => G.limitCarrier.coordinateCoefficient q
        (fun t x v w => G.limitCarrier.metricInner (G.limitFlow.metricAt t) x v w)
          a b (p.1, y)) p.2)) := by
  let P := ContinuousMultilinearMap.compContinuousLinearMapL
    (𝕜 := ℝ) (F := ℝ) (fun _ : Fin r =>
      ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin n)))
  have h := P.continuous.continuousAt.tendsto.comp
    (G.tendsto_coordinate_metricJet q r a b p ht hp)
  have hlim : iteratedFDeriv ℝ r (fun y => G.limitCarrier.coordinateCoefficient q
      (fun t x v w => G.limitCarrier.metricInner (G.limitFlow.metricAt t) x v w)
        a b (p.1, y)) p.2 = P (iteratedFDeriv ℝ r
          (G.limitCarrier.coordinateCoefficient q
            (fun t x v w => G.limitCarrier.metricInner (G.limitFlow.metricAt t) x v w)
              a b) p) := by
    ext v
    exact Poincare.Analysis.iteratedFDeriv_spatial_slice _
      (G.limitFlow.contDiffAt_coordinateCoefficient_metric q a b p ht hp) r v
  rw [← hlim] at h
  apply h.congr'
  filter_upwards [G.eventually_contDiffAt_coordinateCoefficient q p ht hp] with k hk
  ext v
  exact (Poincare.Analysis.iteratedFDeriv_spatial_slice _ (hk a b) r v).symm

theorem tendsto_coordinate_metric_inverse (G : PointedGeometricConvergence S)
    (q : G.limitCarrier.carrier) (p : ℝ × EuclideanSpace ℝ (Fin n))
    (ht : p.1 ∈ Ioo T' T)
    (hp :
      letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
        G.limitCarrier.chartedSpace
      p.2 ∈ (extChartAt (𝓡 n) q).target) :
    Tendsto (fun k => (Matrix.of (fun a b : Fin n =>
      G.limitCarrier.coordinateCoefficient q
        (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k)) a b p))⁻¹)
      atTop (𝓝 ((Matrix.of (fun a b : Fin n =>
        G.limitCarrier.coordinateCoefficient q
          (fun t x v w => G.limitCarrier.metricInner (G.limitFlow.metricAt t) x v w)
            a b p))⁻¹)) := by
  have hg : Tendsto (fun k => Matrix.of (fun a b : Fin n =>
      G.limitCarrier.coordinateCoefficient q
        (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k)) a b p))
      atTop (𝓝 (Matrix.of (fun a b : Fin n =>
        G.limitCarrier.coordinateCoefficient q
          (fun t x v w => G.limitCarrier.metricInner (G.limitFlow.metricAt t) x v w)
            a b p))) := by
    apply tendsto_pi_nhds.mpr
    intro a
    apply tendsto_pi_nhds.mpr
    intro b
    simpa only [iteratedFDeriv_zero_apply, Matrix.of_apply] using
      G.tendsto_coordinate_metricJet_apply q 0 a b p ht hp (fun i => Fin.elim0 i)
  have hdet := G.limitCarrier.coordinateCoefficient_metric_det_ne_zero
    (G.limitFlow.metricAt p.1) q p hp
  have hi : ContinuousAt Ring.inverse
      (Matrix.of (fun a b : Fin n => G.limitCarrier.coordinateCoefficient q
        (fun t x v w => G.limitCarrier.metricInner (G.limitFlow.metricAt t) x v w)
          a b p)).det := by
    rw [show (Ring.inverse : ℝ → ℝ) = Inv.inv from funext Ring.inverse_eq_inv]
    convert! continuousAt_inv₀ hdet using 1
  exact (continuousAt_matrix_inv _ hi).tendsto.comp hg

end PoincareConjecture.PointedGeometricConvergence
