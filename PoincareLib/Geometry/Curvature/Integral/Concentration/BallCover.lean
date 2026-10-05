import PoincareLib.Geometry.Riemannian.Comparison.Covering
import PoincareLib.Geometry.Riemannian.Compactness.IntrinsicMetric
import PoincareLib.Geometry.Riemannian.Curvature.Bounds.Ricci
import PoincareLib.Geometry.Curvature.Integral.Concentration.FiniteCover

/-!
# Concentration in a uniformly bounded ball cover

The relative Bishop--Gromov covering estimate constructs an internal finite
cover of a unit ball. A nonnegative continuous integrand has a covering ball
carrying at least the reciprocal of the cover bound times its unit-ball
integral. This supplies the small-scale concentration step in Petrunin,
Section 4.6, author manuscript pp. 12--14.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Every continuous real function is integrable on a bounded intrinsic ball
of a complete manifold. Connectedness and curvature bounds are unnecessary. -/
theorem integrableOn_ball_of_continuous
    (g : RiemannianMetric n M) (hcomplete : MetricComplete g)
    {h : M → ℝ} (hh : Continuous h) (p : M) (r : ℝ) :
    IntegrableOn h (g.ball p r) g.volumeMeasure := by
  exact (hh.continuousOn.integrableOn_compact
    (g.isCompact_closedBall_of_metricComplete hcomplete p r)).mono_set
      (fun _ hx => (show g.edist p _ < ENNReal.ofReal r from hx).le)

/-- The universal natural covering bound is positive. -/
theorem unitBall_cover_card_bound_pos (n : ℕ) (hn : 1 ≤ n)
    {r : ℝ} (hr : 0 < r) :
    0 < ⌈modelVolume n 1 3 / modelVolume n 1 (r / 2)⌉₊ := by
  apply Nat.ceil_pos.mpr
  exact div_pos (modelVolume_pos hn (by norm_num) (by norm_num))
    (modelVolume_pos hn (by norm_num) (by positivity))

variable [PreconnectedSpace M]

/-- A complete sectional-lower-bounded unit ball has an internal nonempty
cover whose cardinality depends only on dimension and the smaller radius. -/
theorem exists_finset_unitBall_cover
    (g : RiemannianMetric n M) (p : M) (hn : 1 ≤ n)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hcomplete : MetricComplete g) (D : LeviCivitaData g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x v w) :
    ∃ S : Finset M, S.Nonempty ∧ (S : Set M) ⊆ g.ball p 1 ∧
      S.card ≤ ⌈modelVolume n 1 3 / modelVolume n 1 (r / 2)⌉₊ ∧
      g.ball p 1 ⊆ ⋃ q ∈ S, g.ball q r := by
  let : MetricSpace M := g.toMetricSpace
  let : ProperSpace M := g.properSpace_toMetricSpace hcomplete
  let : SecondCountableTopology M := g.secondCountableTopology
  have hcompact : IsCompact (closure (g.ball p (5 * 1))) := by
    rw [← g.toMetricSpace_ball]
    exact (isCompact_closedBall p (5 * 1)).of_isClosed_subset
      isClosed_closure Metric.closure_ball_subset_closedBall
  obtain ⟨S, hS, hcard, _, hcover⟩ :=
    g.exists_finset_cover_of_precompact_ball p hn zero_lt_one hr hr1 (by norm_num : (0 : ℝ) ≤ 1)
      hcompact D (fun x _ v =>
        D.ricci_quadratic_lower_bound_of_sectionalCurvature_lower_bound x 1 (hsec x) v)
  have hp : p ∈ g.ball p 1 := by
    rw [← g.toMetricSpace_ball]
    exact Metric.mem_ball_self zero_lt_one
  obtain ⟨q, hq, _⟩ := mem_iUnion₂.mp (hcover hp)
  refine ⟨S, ⟨q, hq⟩, hS, ?_, hcover⟩
  simpa only [mul_one] using hcard

/-- Some radius-`r` ball centered inside the unit ball carries a uniform
fraction of the integral of any continuous nonnegative real function. -/
theorem exists_unitBall_integral_concentration
    (g : RiemannianMetric n M) (p : M) (hn : 1 ≤ n)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hcomplete : MetricComplete g) (D : LeviCivitaData g)
    (hsec : ∀ x (v w : TangentSpace (𝓡 n) x), -1 ≤ D.sectionalCurvature x v w)
    {h : M → ℝ} (hh : Continuous h) (hhn : ∀ x, 0 ≤ h x) :
    ∃ q ∈ g.ball p 1,
      (∫ x in g.ball p 1, h x ∂g.volumeMeasure) ≤
        (⌈modelVolume n 1 3 / modelVolume n 1 (r / 2)⌉₊ : ℝ) *
          ∫ x in g.ball q r, h x ∂g.volumeMeasure := by
  classical
  let : MetricSpace M := g.toMetricSpace
  have hm (q : M) (s : ℝ) : MeasurableSet (g.ball q s) := by
    rw [← g.toMetricSpace_ball]
    exact Metric.isOpen_ball.measurableSet
  obtain ⟨S, hSne, hS, hcard, hcover⟩ :=
    g.exists_finset_unitBall_cover p hn hr hr1 hcomplete D hsec
  have hsum := Poincare.CurvatureIntegral.integral_le_sum_of_finset_cover
    (hm p 1) S (fun q => g.ball q r)
    (fun q _ => hm q r) hhn (g.integrableOn_ball_of_continuous hcomplete hh p 1)
    (fun q _ => g.integrableOn_ball_of_continuous hcomplete hh q r) hcover
  obtain ⟨q, hq, hmax⟩ :=
    S.exists_max_image (fun q => ∫ x in g.ball q r, h x ∂g.volumeMeasure) hSne
  refine ⟨q, hS hq, hsum.trans ?_⟩
  calc
    (∑ y ∈ S, ∫ x in g.ball y r, h x ∂g.volumeMeasure) ≤
        ∑ _y ∈ S, ∫ x in g.ball q r, h x ∂g.volumeMeasure :=
      Finset.sum_le_sum fun y hy => hmax y hy
    _ = (S.card : ℝ) * ∫ x in g.ball q r, h x ∂g.volumeMeasure := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      (integral_nonneg hhn)

end PoincareMT.RiemannianMetric
