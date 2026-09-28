import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import Mathlib.Topology.MetricSpace.HausdorffDistance









noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric



theorem exists_infDist_hessian_upper_support
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ y : M, ∀ u v : TangentSpace (𝓡 n) y,
      -K ≤ D.sectionalCurvature y u v)
    (S : Set M) (hS : IsClosed S) (hSne : S.Nonempty) (x : M) (hx : x ∉ S) :
    letI := g.toMetricSpace
    ∃ (U : Set M) (rho : M → ℝ), IsOpen U ∧ x ∈ U ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho U ∧
      rho x = Metric.infDist x S ∧
      (∀ y ∈ U, Metric.infDist y S ≤ rho y) ∧
      g.inner x (D.gradient rho x) (D.gradient rho x) = 1 ∧
      ∀ w : TangentSpace (𝓡 n) x,
        D.hessian rho x w w ≤
          (4 / (3 * Metric.infDist x S) + K * Metric.infDist x S / 4) *
            g.inner x w w := by
  let := g.toMetricSpace
  let : ProperSpace M := g.properSpace_toMetricSpace hcomplete
  obtain ⟨p, hp, hnearest⟩ := hS.exists_infDist_eq_dist hSne x
  have hpx : p ≠ x := by
    rintro rfl
    exact hx hp
  have hdist : (g.edist p x).toReal = Metric.infDist x S := by
    rw [hnearest]
    change dist p x = dist x p
    exact dist_comm _ _
  obtain ⟨U, rho, hU, hxU, hsmooth, hvalue, hupper, hgradient, hhessian⟩ :=
    g.exists_distance_hessian_upper_support D hcomplete hK hsec p x hpx
  refine ⟨U, rho, hU, hxU, hsmooth, hvalue.trans hdist, ?_, hgradient, ?_⟩
  · intro y hy
    calc
      Metric.infDist y S ≤ dist y p := Metric.infDist_le_dist_of_mem hp
      _ = (g.edist p y).toReal := dist_comm _ _
      _ ≤ rho y := hupper y hy
  · intro w
    simpa only [hdist] using hhessian w

end PoincareConjecture.RiemannianMetric
