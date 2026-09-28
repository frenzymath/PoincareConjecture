import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.BootstrapAdapter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.SingularRegularLimit

open SpacetimeBounds SpacetimeBounds.Bootstrap

theorem tendsto_metricTwoJet_of_bilinear_jets
    {n : ℕ} {ι : Type*} {l : Filter ι}
    {B : ι → EuclideanSpace ℝ (Fin n) → MetricCoefficient n}
    {BT : EuclideanSpace ℝ (Fin n) → MetricCoefficient n}
    (x : EuclideanSpace ℝ (Fin n))
    (hjets : ∀ r : ℕ, r ≤ 2 →
      Tendsto (fun i => iteratedFDeriv ℝ r (B i) x) l
        (𝓝 (iteratedFDeriv ℝ r BT x))) :
    Tendsto (fun i => metricTwoJet (B i) x) l (𝓝 (metricTwoJet BT x)) := by
  have hpi : Tendsto
      (fun i => spatialJet 2 (fun p : ℝ × EuclideanSpace ℝ (Fin n) => B i p.2) (0, x)) l
      (𝓝 (spatialJet 2 (fun p : ℝ × EuclideanSpace ℝ (Fin n) => BT p.2) (0, x))) :=
    tendsto_pi_nhds.mpr (fun r => hjets r (by omega))
  have h := ((twoJetProjection n).continuous.tendsto _).comp hpi
  simpa only [Function.comp_def, twoJetProjection_spatialJet] using h

theorem tendsto_ricci_of_chart_metric_jets
    {n : ℕ} {M X ι : Type*} {l : Filter ι}
    [TopologicalSpace M] [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ X]
    (gseq : ι → RiemannianMetric n M) (Dseq : ∀ i, LeviCivitaData (gseq i))
    (g : RiemannianMetric n X) (D : LeviCivitaData g)
    (qM : M) (qX : X) (p u v : EuclideanSpace ℝ (Fin n))
    (hpM : p ∈ (extChartAt (𝓡 n) qM).target)
    (hpX : p ∈ (extChartAt (𝓡 n) qX).target)
    (hjets : ∀ r : ℕ, r ≤ 2 →
      Tendsto (fun i => iteratedFDeriv ℝ r
        ((gseq i).pullbackCoefficients (extChartAt (𝓡 n) qM).symm) p) l
        (𝓝 (iteratedFDeriv ℝ r
          (g.pullbackCoefficients (extChartAt (𝓡 n) qX).symm) p))) :
    Tendsto (fun i => (Dseq i).ricci ((extChartAt (𝓡 n) qM).symm p)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) qM).symm p u)
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) qM).symm p v)) l
      (𝓝 (D.ricci ((extChartAt (𝓡 n) qX).symm p)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) qX).symm p u)
        (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) qX).symm p v))) := by
  have hiM (z) (hz : z ∈ (extChartAt (𝓡 n) qM).target) :=
    Poincare.Manifold.VectorField.isInvertible_mfderiv_extChartAt_symm (I := 𝓡 n) hz
  have hiX (z) (hz : z ∈ (extChartAt (𝓡 n) qX).target) :=
    Poincare.Manifold.VectorField.isInvertible_mfderiv_extChartAt_symm (I := 𝓡 n) hz
  have hJ : (metricTwoJet (g.pullbackCoefficients (extChartAt (𝓡 n) qX).symm) p).1.IsInvertible :=
    g.isInvertible_pullbackCoefficients (hiX p hpX).injective
  have h := (contDiffAt_jetRicci hJ u v).continuousAt.tendsto.comp
    (tendsto_metricTwoJet_of_bilinear_jets p hjets)
  rw [jetRicci_metricTwoJet_pullback D (isOpen_extChartAt_target qX)
    (contMDiffOn_extChartAt_symm qX) hiX hpX] at h
  exact h.congr (fun i => jetRicci_metricTwoJet_pullback (Dseq i)
    (isOpen_extChartAt_target qM) (contMDiffOn_extChartAt_symm qM) hiM hpM u v)

end PoincareConjecture.SingularRegularLimit
