import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.Ellipticity
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.DerivativeControl
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.FiniteOrder.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.PrecompactGauss













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.PointedRicciFlowCompactnessHypotheses



theorem eventually_uniform_zero_time_exponential_metric_jet_bound_of_local_derivative_estimates
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hShi : LocalCurvatureDerivativeEstimates.{0})
    {A ρ R : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρR : ρ < R) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      ∀ p ∈ F.zeroBall A,
        ∀ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
        ∀ Φ : PartialDiffeomorph (𝓡 n) (𝓡 n)
            (EuclideanSpace ℝ (Fin n)) C.carrier ∞,
          Φ.source = Metric.ball 0 R → Φ.target = (F.metricAt 0).ball p R →
          Φ 0 = p →
          (∀ u v, (F.metricAt 0).pullbackCoefficients
            (extChartAt (𝓡 n) p).symm (extChartAt (𝓡 n) p p)
            (L u) (L v) = inner ℝ u v) →
          HasFDerivAt (fun w => extChartAt (𝓡 n) p (Φ w))
            L.toContinuousLinearMap 0 →
          (∀ w ∈ Metric.ball 0 R,
            (F.metricAt 0).IsGeodesicOn (fun t => Φ (t • w))
              {t : ℝ | t • w ∈ Metric.ball 0 R}) →
          ∀ x ∈ Metric.closedBall 0 ρ,
            ‖iteratedFDeriv ℝ m ((F.metricAt 0).pullbackCoefficients Φ) x‖ ≤ B := by
  have hR : 0 < R := hρ.trans hρR
  choose D hD hcurv using fun l =>
    H.eventually_zero_time_curvatureDerivativeNorm_le_of_local_derivative_estimates
      hShi (A + R) (by positivity) l
  obtain ⟨B, hB, hbound⟩ := CoordinateExponential.exists_uniform_pullback_metric_jet_bound
    n m hρ hρR D (fun l => (hD l).le)
  refine ⟨B, hB, ?_⟩
  filter_upwards [(eventually_all_finite (Set.finite_Iic m)).mpr
    (fun l _ => hcurv l)] with k hk
  let C := H.sequence.carrier k
  let F := H.sequence.flow k
  let : TopologicalSpace C.carrier := C.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  let : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  let g := F.metricAt 0
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : C.carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  dsimp only
  intro p hp L Φ hsource htarget hzero hL hderiv hgeo
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ Φ (Metric.ball 0 R) := by
    simpa only [hsource] using Φ.contMDiffOn
  have hnorm := g.pullbackCoefficients_zero_of_orthonormal p
    (he.contMDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR)))
    hzero hderiv hL
  apply hbound g (F.flow.connection 0) Φ he
  · intro x hx
    exact ⟨(Φ.isLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞
      (hsource.symm ▸ hx)).mfderivToContinuousLinearEquiv (by simp), rfl⟩
  · exact hnorm
  · exact CoordinateExponential.gauss_identity_of_radial_family g he hgeo
      (fun v hv t ht =>
        g.tangentNorm_radial_of_normalized_exponential p L hzero hL hderiv hgeo hv ht)
  · intro l hl x hx
    apply hk l hl (Φ x)
    have hxp : Φ x ∈ g.ball p R := by
      rw [← htarget]
      exact Φ.map_source (hsource.symm ▸ hx)
    change g.edist F.base (Φ x) < ENNReal.ofReal (A + R)
    rw [ENNReal.ofReal_add hA.le hR.le]
    exact Manifold.riemannianEDist_triangle.trans_lt (ENNReal.add_lt_add hp hxp)


theorem eventually_uniform_zero_time_exponential_metric_jet_bound
    {n : ℕ} {T' T : ℝ}
    (H : PointedRicciFlowCompactnessHypotheses n T' T)
    (hM04 : RicciFlowCurvatureTheory.{0})
    {A ρ R : ℝ} (hA : 0 < A) (hρ : 0 < ρ) (hρR : ρ < R) (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop,
      let C := H.sequence.carrier k
      let F := H.sequence.flow k
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
      ∀ p ∈ F.zeroBall A,
        ∀ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
        ∀ Φ : PartialDiffeomorph (𝓡 n) (𝓡 n)
            (EuclideanSpace ℝ (Fin n)) C.carrier ∞,
          Φ.source = Metric.ball 0 R → Φ.target = (F.metricAt 0).ball p R →
          Φ 0 = p →
          (∀ u v, (F.metricAt 0).pullbackCoefficients
            (extChartAt (𝓡 n) p).symm (extChartAt (𝓡 n) p p)
            (L u) (L v) = inner ℝ u v) →
          HasFDerivAt (fun w => extChartAt (𝓡 n) p (Φ w))
            L.toContinuousLinearMap 0 →
          (∀ w ∈ Metric.ball 0 R,
            (F.metricAt 0).IsGeodesicOn (fun t => Φ (t • w))
              {t : ℝ | t • w ∈ Metric.ball 0 R}) →
          ∀ x ∈ Metric.closedBall 0 ρ,
            ‖iteratedFDeriv ℝ m ((F.metricAt 0).pullbackCoefficients Φ) x‖ ≤ B :=
  H.eventually_uniform_zero_time_exponential_metric_jet_bound_of_local_derivative_estimates
    hM04.local_derivative_estimates hA hρ hρR m

end PoincareConjecture.PointedRicciFlowCompactnessHypotheses
