import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.RadiusSelection
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.MovingAnnularStability

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open Poincare.GromovHausdorff Poincare.CurvatureIntegral
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RiemannianMetric

theorem tendsto_badAscentRadius_zero_of_moving_centers
    {n : ℕ} {M : ℕ → Type u} [∀ j, TopologicalSpace (M j)]
    [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, PoincareConjecture.RiemannianMetric n (M j))
    (D : ∀ j, PoincareConjecture.LeviCivitaData (g j))
    (hc : ∀ j, PoincareConjecture.MetricComplete (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (p : ∀ j, M j) {Y : BasedMetricSpaceBundle.{u}} [ProperSpace Y.carrier]
    {L : ℝ} (hL : 0 < L) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0)) (hpos : ∀ j, 0 < L + δ j)
    (S : VaryingRealizationSequence
      (fun j => (ballModel ((g j).toBasedMetricSpace (p j))
        (L + δ j) (hpos j)).toBasedMetricSpaceBundle)
      (ballModel Y L hL).toBasedMetricSpaceBundle)
    (u : ∀ j, (ballModel ((g j).toBasedMetricSpace (p j))
      (L + δ j) (hpos j)).carrier)
    (u₀ : (ballModel Y L hL).carrier) (hu : S.PointConverges u u₀)
    {b c c' : ℝ} (hb : 0 < b) (hcc' : c < c')
    (hroom : dist Y.base u₀.val + 2 * b < L)
    (hascent : ∀ y : Y.carrier, 0 < dist u₀.val y → dist u₀.val y ≤ b →
      HasLocalDistanceAscent c' u₀.val y) :
    Tendsto (fun j => letI := (g j).toMetricSpace; badAscentRadius c b (u j).val)
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsource := eventually_annular_distance_ascent_of_moving_centers
    g D hc (K := 1) zero_le_one hsec p hL δ hδ hpos S u u₀ hu
    (half_pos hε) hb hcc' hroom
    (fun y hy hyb => hascent y ((half_pos hε).trans_le hy) hyb)
  filter_upwards [hsource] with j hj
  let := (g j).toMetricSpace
  change dist (badAscentRadius c b (u j).val) 0 < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (badAscentRadius_nonneg c b (u j).val)]
  have hbound : badAscentRadius c b (u j).val ≤ ε / 2 :=
    badAscentRadius_le_of_annular_ascent (half_pos hε).le
      (fun y hy hyb => hj y hy.le hyb)
  exact hbound.trans_lt (half_lt_self hε)

end PoincareConjecture.RiemannianMetric
