import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.AnnulusApproximation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.ConeTopology

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Topology NNReal ENNReal Manifold ContDiff

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X}

theorem annulusConeRelation_distortion_of_uniform_ray_bound
    (hcomparison : RayComparison p) {L τ δ R : ℝ} (hL : 0 < L)
    (hlimit : ∀ r s : ℝ≥0, r ≤ R.toNNReal → s ≤ R.toNNReal →
      ∀ γ η : basedMinimizingRays p,
        |dist (rayExtension γ (r * L)) (rayExtension η (s * L)) / L -
          dist (asymptoticConeRayProjection hcomparison (r, γ))
            (asymptoticConeRayProjection hcomparison (s, η))| < δ)
    {x y : X} {z w : AsymptoticCone p hcomparison}
    (hxbound : dist p x / L ≤ R) (hybound : dist p y / L ≤ R)
    (hx : annulusConeRelation hcomparison L τ x z)
    (hy : annulusConeRelation hcomparison L τ y w) :
    |dist x y / L - dist z w| < 2 * τ + δ := by
  obtain ⟨γ, hγ, hx⟩ := hx
  obtain ⟨η, hη, hy⟩ := hy
  have htime (q : X) : ((dist p q / L).toNNReal : ℝ) * L = dist p q := by
    rw [Real.coe_toNNReal _ (div_nonneg dist_nonneg hL.le), div_mul_cancel₀ _ hL.ne']
  have herror := hlimit (dist p x / L).toNNReal (dist p y / L).toNNReal
    (Real.toNNReal_mono hxbound) (Real.toNNReal_mono hybound) γ η
  rw [htime, htime, hγ, hη] at herror
  have hsource : |dist x y / L - dist (rayExtension γ (dist p x)) (rayExtension η (dist p y)) / L| ≤
      dist x (rayExtension γ (dist p x)) / L + dist y (rayExtension η (dist p y)) / L := by
    rw [← sub_div, abs_div, abs_of_pos hL, ← add_div]
    exact div_le_div_of_nonneg_right
      (by simpa only [Real.dist_eq] using
        dist_dist_dist_le x y (rayExtension γ (dist p x)) (rayExtension η (dist p y))) hL.le
  have htri := abs_sub_le (dist x y / L)
    (dist (rayExtension γ (dist p x)) (rayExtension η (dist p y)) / L) (dist z w)
  linarith

end Poincare.AncientVolume.ScalarRatio

namespace PoincareConjecture.RiemannianMetric

open Poincare.AncientVolume.ScalarRatio

theorem exists_closedBallConeRelation_approximation_of_metricComplete
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    letI := g.toMetricSpace
    let hcomparison := g.rayComparison_of_metricComplete D hc hsec p
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      (∀ x : rescaledClosedAnnulus p L 0 R,
        ∃ z : asymptoticConeClosedAnnulus hcomparison 0 R,
          annulusConeRelation hcomparison L (ε / 4) (x : M) z) ∧
      (∀ z : asymptoticConeClosedAnnulus hcomparison 0 R,
        ∃ x : rescaledClosedAnnulus p L 0 R,
          annulusConeRelation hcomparison L (ε / 4) (x : M) z) ∧
      (∀ (x : rescaledClosedAnnulus p L 0 R)
        (z : asymptoticConeClosedAnnulus hcomparison 0 R),
        annulusConeRelation hcomparison L (ε / 4) (x : M) z →
          (asymptoticConeRadius hcomparison z : ℝ) = (g.edist p (x : M)).toReal / L) ∧
      ∀ (x y : rescaledClosedAnnulus p L 0 R)
        (z w : asymptoticConeClosedAnnulus hcomparison 0 R),
        annulusConeRelation hcomparison L (ε / 4) (x : M) z →
        annulusConeRelation hcomparison L (ε / 4) (y : M) w →
        |(g.edist (x : M) (y : M)).toReal / L - dist z w| < ε := by
  let := g.toMetricSpace
  let := g.properSpace_toMetricSpace hc
  let hcomparison := g.rayComparison_of_metricComplete D hc hsec p
  obtain ⟨A, hA, happrox⟩ := g.exists_uniform_ray_approximation_on_annuli D hc hsec p
    (a := ε / 16) (b := R) (by positivity) hR (show 0 < ε / 4 by positivity)
  obtain ⟨B, _, huniform⟩ := exists_uniform_cone_distance_bound hcomparison R.toNNReal
    (show 0 < ε / 2 by positivity)
  obtain ⟨γ₀⟩ := g.nonempty_basedMinimizingRays hc p
  refine ⟨max A B, hA.trans_le (le_max_left _ _), ?_⟩
  intro L hL
  have hLpos : 0 < L := (hA.trans_le (le_max_left A B)).trans_le hL
  refine ⟨?_, annulusConeRelation_surjective hcomparison hLpos (by positivity), ?_, ?_⟩
  · intro x
    have hnear : ∃ γ : basedMinimizingRays p,
        dist (x : M) (rayExtension γ (dist p (x : M))) / L < ε / 4 := by
      by_cases hx : (ε / 16) * L ≤ dist p (x : M)
      · obtain ⟨ray, hray0, hray, herr⟩ :=
          happrox L ((le_max_left A B).trans hL) x hx ((div_le_iff₀ hLpos).mp x.2.2)
        refine ⟨g.basedMinimizingRayOfEdist ray hray0 hray, ?_⟩
        rw [g.rayExtension_basedMinimizingRayOfEdist ray hray0 hray dist_nonneg]
        exact herr
      · refine ⟨γ₀, (div_lt_iff₀ hLpos).mpr ?_⟩
        have hd : dist p (rayExtension γ₀ (dist p (x : M))) = dist p (x : M) := by
          simpa only [rayExtension_zero, zero_sub, abs_neg, abs_of_nonneg dist_nonneg] using
            rayExtension_dist γ₀ le_rfl dist_nonneg
        have hh := dist_triangle (x : M) p (rayExtension γ₀ (dist p (x : M)))
        rw [hd, dist_comm (x : M) p] at hh
        nlinarith [lt_of_not_ge hx]
    obtain ⟨γ, hγ⟩ := hnear
    let z := asymptoticConeRayProjection hcomparison ((dist p (x : M) / L).toNNReal, γ)
    have hz : z ∈ asymptoticConeClosedAnnulus hcomparison 0 R := by
      change 0 ≤ ((dist p (x : M) / L).toNNReal : ℝ) ∧
        ((dist p (x : M) / L).toNNReal : ℝ) ≤ R
      rw [Real.coe_toNNReal _ (div_nonneg dist_nonneg hLpos.le)]
      exact x.2
    exact ⟨⟨z, hz⟩, γ, rfl, hγ⟩
  · intro x z hrel
    exact annulusConeRelation_radius hcomparison hLpos hrel
  · intro x y z w hx hy
    have hlimit (r s : ℝ≥0) (hr : r ≤ R.toNNReal) (hs : s ≤ R.toNNReal)
        (γ η : basedMinimizingRays p) :
        |dist (rayExtension γ (r * L)) (rayExtension η (s * L)) / L -
          dist (asymptoticConeRayProjection hcomparison (r, γ))
            (asymptoticConeRayProjection hcomparison (s, η))| < ε / 2 := by
      have hh := huniform L ((le_max_right A B).trans hL) r s hr hs γ η
      rw [abs_of_nonneg hh.1]
      exact hh.2
    have hh := annulusConeRelation_distortion_of_uniform_ray_bound hcomparison hLpos
      hlimit x.2.2 y.2.2 hx hy
    change |dist (x : M) (y : M) / L -
      dist (z : AsymptoticCone p hcomparison) (w : AsymptoticCone p hcomparison)| < ε
    linarith only [hh]

end PoincareConjecture.RiemannianMetric
