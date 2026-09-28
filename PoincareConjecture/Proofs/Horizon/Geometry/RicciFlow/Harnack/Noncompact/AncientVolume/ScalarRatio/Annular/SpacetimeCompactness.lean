import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.SpacetimeBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.HalfCylinder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.RicciFlow

theorem exists_ancient_exponential_spacetime_coefficient_subsequence
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) {K S : ℝ} (hK : 0 < K) (hS : 0 < S)
    (F : ℕ → RicciFlow n M (Iic 0))
    (hcomplete : ∀ k t, t ≤ 0 → MetricComplete ((F k).metric t))
    (hoperator : ∀ k t, t ≤ 0 → ∀ x,
      ((F k).connection t).NonnegativeCurvatureOperator x)
    (p : ℕ → M)
    (hcurv : ∀ k t, t ≤ 0 → ∀ x ∈ ((F k).metric 0).ball (p k) (2 * S),
      ((F k).connection t).curvatureTensorNorm x ≤ K)
    (L : ℕ → EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (hsource : ∀ k, (Φ k).source = Metric.ball 0 S)
    (hzero : ∀ k, Φ k 0 = p k)
    (hL : ∀ k v w, ((F k).metric 0).pullbackCoefficients
      (extChartAt (𝓡 n) (p k)).symm (extChartAt (𝓡 n) (p k) (p k))
        (L k v) (L k w) = inner ℝ v w)
    (hderiv : ∀ k, HasFDerivAt (fun w => extChartAt (𝓡 n) (p k) (Φ k w))
      (L k).toContinuousLinearMap 0)
    (hgeo : ∀ k w, w ∈ Metric.ball 0 S →
      ((F k).metric 0).IsGeodesicOn (fun t => Φ k (t • w))
        {t : ℝ | t • w ∈ Metric.ball 0 S})
    (hdist : ∀ k w, w ∈ Metric.ball 0 S →
      ((F k).metric 0).edist (p k) (Φ k w) = ENNReal.ofReal ‖w‖) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < S / 2 ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ B : ℝ × EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
        ContDiffOn ℝ ∞ B (Iic 0 ×ˢ Metric.closedBall 0 ρ) ∧
        ∀ m C, IsCompact C → C ⊆ Iic 0 ×ˢ Metric.closedBall 0 ρ → TendstoUniformlyOn
          (fun k => iteratedFDerivWithin ℝ m
            (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
              ((F (σ k)).metric z.1).pullbackCoefficients (Φ (σ k)) z.2)
            (Iic 0 ×ˢ Metric.closedBall 0 ρ))
          (iteratedFDerivWithin ℝ m B (Iic 0 ×ˢ Metric.closedBall 0 ρ)) atTop C := by
  obtain ⟨ρ, hρ, hρS, hbounds⟩ := exists_ancient_exponential_spacetime_jet_bounds
    hC hK hS F hcomplete hoperator p hcurv L Φ hsource hzero hL hderiv hgeo hdist
  have hsmooth (k : ℕ) : ContDiffOn ℝ ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        ((F k).metric z.1).pullbackCoefficients (Φ k) z.2) (Iic 0 ×ˢ Metric.ball 0 S) := by
    apply (F k).contDiffOn_pullbackCoefficients_within Metric.isOpen_ball
    simpa only [hsource k] using (Φ k).contMDiffOn
  obtain ⟨σ, hσ, B, hB, hjets⟩ :=
    Poincare.AncientVolume.exists_smooth_subsequence_on_ancient_halfCylinder
      hρ (by linarith : ρ < S)
      (fun k (z : ℝ × EuclideanSpace ℝ (Fin n)) =>
        ((F k).metric z.1).pullbackCoefficients (Φ k) z.2) hsmooth hbounds
  exact ⟨ρ, hρ, hρS, σ, hσ, B, hB, hjets⟩

end PoincareConjecture.RicciFlow
