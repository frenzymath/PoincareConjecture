import PoincareLib.Geometry.Curvature.Integral.Concentration.RadiusSelection
import PoincareLib.Geometry.Riemannian.Distance.Smoothing.Directional.AnnularStability

/-!
# Vanishing bad-ascent radii in pointed limits

A punctured ascent neighborhood in the limit gives eventual source ascent
on every fixed closed annulus, at any strictly smaller rate. Taking the
supremum of the actual bad-point distances makes their radius tend to zero.
The strict rate loss is retained explicitly; no same-rate stability is used.

Reference: Petrunin (2009), Section 3.7, author manuscript p. 7.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Topology
open Poincare.GromovHausdorff Poincare.CurvatureIntegral
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.RiemannianMetric

/-- A limit punctured ascent radius strictly larger than the outer cutoff
forces the actual source bad-ascent radii to vanish, with a strict rate loss. -/
theorem tendsto_badAscentRadius_zero_of_pointedGHConvergesUnbounded
    {n : ℕ} {M : ℕ → Type u} [∀ j, TopologicalSpace (M j)]
    [∀ j, T3Space (M j)] [∀ j, PreconnectedSpace (M j)]
    [∀ j, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M j)]
    [∀ j, IsManifold (𝓡 n) ∞ (M j)]
    (g : ∀ j, PoincareMT.RiemannianMetric n (M j))
    (D : ∀ j, PoincareMT.LeviCivitaData (g j))
    (hc : ∀ j, PoincareMT.MetricComplete (g j))
    (hsec : ∀ j (x : M j) (v w : TangentSpace (𝓡 n) x),
      -1 ≤ (D j).sectionalCurvature x v w)
    (p : ∀ j, M j) {Y : BasedMetricSpaceBundle.{u}} [ProperSpace Y.carrier]
    (hconv : PointedGHConvergesUnbounded
      (fun j => (g j).toBasedMetricSpace (p j)) Y)
    {b R c c' : ℝ} (hbR : b < R) (hcc' : c < c')
    (hascent : ∀ y : Y.carrier, 0 < dist Y.base y → dist Y.base y < R →
      HasLocalDistanceAscent c' Y.base y) :
    Tendsto (fun j => letI := (g j).toMetricSpace; badAscentRadius c b (p j))
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hsource := eventually_annular_distance_ascent_of_pointedGHConvergesUnbounded
    g D hc (K := 1) zero_le_one hsec p hconv (half_pos hε) hcc'
    (R := b) (fun y hy hyb =>
      hascent y ((half_pos hε).trans_le hy) (hyb.trans_lt hbR))
  filter_upwards [hsource] with j hj
  let := (g j).toMetricSpace
  change dist (badAscentRadius c b (p j)) 0 < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (badAscentRadius_nonneg c b (p j))]
  have hbound : badAscentRadius c b (p j) ≤ ε / 2 :=
    badAscentRadius_le_of_annular_ascent (half_pos hε).le
      (fun y hy hyb => hj y hy.le hyb)
  exact hbound.trans_lt (half_lt_self hε)

end PoincareMT.RiemannianMetric
