import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.UniformRayDistance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.RayDensity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.Metric.RiemannianLink













noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology NNReal

namespace Poincare.AncientVolume.ScalarRatio

variable {X : Type*} [MetricSpace X] {p : X}



def sphereLinkRelation (hcomparison : RayComparison p) (L τ : ℝ)
    (x : Metric.sphere p L) (z : AsymptoticLink p hcomparison) : Prop :=
  ∃ γ : basedMinimizingRays p, asymptoticLinkProjection hcomparison γ = z ∧
    dist (x : X) (rayExtension γ L) / L < τ



theorem sphereLinkRelation_surjective (hcomparison : RayComparison p)
    {L τ : ℝ} (hL : 0 < L) (hτ : 0 < τ) (z : AsymptoticLink p hcomparison) :
    ∃ x : Metric.sphere p L, sphereLinkRelation hcomparison L τ x z := by
  obtain ⟨γ, rfl⟩ := surjective_asymptoticLinkProjection hcomparison z
  have hx : rayExtension γ L ∈ Metric.sphere p L := by
    rw [Metric.mem_sphere]
    simpa only [rayExtension_zero, sub_zero, abs_of_pos hL] using
      rayExtension_dist γ hL.le (le_refl 0)
  refine ⟨⟨rayExtension γ L, hx⟩, γ, rfl, ?_⟩
  simpa only [dist_self, zero_div] using hτ

private theorem sphereLinkRelation_distortion
    (hcomparison : RayComparison p) {L τ δ : ℝ} (hL : 0 < L)
    (hlimit : ∀ γ η : basedMinimizingRays p,
      |dist (rayExtension γ L) (rayExtension η L) / L - asymptoticRayDistance γ η| < δ)
    {x y : Metric.sphere p L} {z w : AsymptoticLink p hcomparison}
    (hx : sphereLinkRelation hcomparison L τ x z)
    (hy : sphereLinkRelation hcomparison L τ y w) :
    |dist (x : X) (y : X) / L - dist z w| < 2 * τ + δ := by
  obtain ⟨γ, rfl, hx⟩ := hx
  obtain ⟨η, rfl, hy⟩ := hy
  rw [dist_asymptoticLinkProjection]
  have hsource :
      |dist (x : X) (y : X) / L - dist (rayExtension γ L) (rayExtension η L) / L| ≤
        dist (x : X) (rayExtension γ L) / L + dist (y : X) (rayExtension η L) / L := by
    rw [← sub_div, abs_div, abs_of_pos hL, ← add_div]
    apply div_le_div_of_nonneg_right _ hL.le
    simpa only [Real.dist_eq] using
      dist_dist_dist_le (x : X) (y : X) (rayExtension γ L) (rayExtension η L)
  calc
    _ ≤ |dist (x : X) (y : X) / L - dist (rayExtension γ L) (rayExtension η L) / L| +
        |dist (rayExtension γ L) (rayExtension η L) / L - asymptoticRayDistance γ η| :=
      abs_sub_le _ _ _
    _ ≤ (dist (x : X) (rayExtension γ L) / L + dist (y : X) (rayExtension η L) / L) +
        |dist (rayExtension γ L) (rayExtension η L) / L - asymptoticRayDistance γ η| :=
      add_le_add hsource le_rfl
    _ < _ := by linarith [hlimit γ η]




theorem exists_sphereLinkRelation_approximation [ProperSpace X]
    (hcomparison : RayComparison p)
    (hdensity : ∀ τ : ℝ, 0 < τ → ∃ R : ℝ, 0 < R ∧
      ∀ x : X, R ≤ dist p x → ∃ γ : basedMinimizingRays p,
        dist x (rayExtension γ (dist p x)) / dist p x < τ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      (∀ x : Metric.sphere p L, ∃ z : AsymptoticLink p hcomparison,
        sphereLinkRelation hcomparison L (ε / 4) x z) ∧
      (∀ z : AsymptoticLink p hcomparison, ∃ x : Metric.sphere p L,
        sphereLinkRelation hcomparison L (ε / 4) x z) ∧
      ∀ (x y : Metric.sphere p L) (z w : AsymptoticLink p hcomparison),
        sphereLinkRelation hcomparison L (ε / 4) x z →
        sphereLinkRelation hcomparison L (ε / 4) y w →
        |dist (x : X) (y : X) / L - dist z w| < ε := by
  obtain ⟨R, hR, hdense⟩ := hdensity (ε / 4) (by positivity)
  obtain ⟨S, _, huniform⟩ := exists_uniform_normalized_ray_distance_bound hcomparison
    (show 0 < ε / 2 by positivity)
  refine ⟨max R S, hR.trans_le (le_max_left _ _), ?_⟩
  intro L hL
  have hLpos : 0 < L := (hR.trans_le (le_max_left R S)).trans_le hL
  refine ⟨?_, sphereLinkRelation_surjective hcomparison hLpos (by positivity), ?_⟩
  · intro x
    have hpx : dist p (x : X) = L := (dist_comm _ _).trans x.2
    have hfar : R ≤ dist p (x : X) := by
      rw [hpx]
      exact (le_max_left R S).trans hL
    obtain ⟨γ, hγ⟩ := hdense (x : X) hfar
    refine ⟨asymptoticLinkProjection hcomparison γ, γ, rfl, ?_⟩
    simpa only [hpx] using hγ
  · intro x y z w hx hy
    have hlimit (γ η : basedMinimizingRays p) :
        |dist (rayExtension γ L) (rayExtension η L) / L - asymptoticRayDistance γ η| < ε / 2 := by
      have h := huniform L ((le_max_right R S).trans hL) γ η
      rw [abs_of_nonneg h.1]
      exact h.2
    have h := sphereLinkRelation_distortion hcomparison hLpos hlimit hx hy
    linarith

end Poincare.AncientVolume.ScalarRatio

open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture.RiemannianMetric

open Poincare.AncientVolume.ScalarRatio





theorem exists_sphereLinkRelation_approximation_of_metricComplete
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature) (p : M)
    {ε : ℝ} (hε : 0 < ε) :
    letI := g.toMetricSpace
    let hcomparison := g.rayComparison_of_metricComplete D hc hsec p
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      Nonempty (Metric.sphere p L) ∧
      (∀ x : Metric.sphere p L, ∃ z : AsymptoticLink p hcomparison,
        sphereLinkRelation hcomparison L (ε / 4) x z) ∧
      (∀ z : AsymptoticLink p hcomparison, ∃ x : Metric.sphere p L,
        sphereLinkRelation hcomparison L (ε / 4) x z) ∧
      ∀ (x y : Metric.sphere p L) (z w : AsymptoticLink p hcomparison),
        sphereLinkRelation hcomparison L (ε / 4) x z →
        sphereLinkRelation hcomparison L (ε / 4) y w →
        |(g.edist (x : M) (y : M)).toReal / L - dist z w| < ε := by
  let := g.toMetricSpace
  let := g.properSpace_toMetricSpace hc
  let hcomparison := g.rayComparison_of_metricComplete D hc hsec p
  have hdensity : ∀ τ : ℝ, 0 < τ → ∃ R : ℝ, 0 < R ∧
      ∀ x : M, R ≤ dist p x → ∃ γ : basedMinimizingRays p,
        dist x (rayExtension γ (dist p x)) / dist p x < τ := by
    intro τ hτ
    obtain ⟨R, hR, hclose⟩ := g.exists_uniform_sublinear_ray_approximation D hc hsec p hτ
    refine ⟨R, hR, ?_⟩
    intro x hx
    obtain ⟨ray, hzero, hmin, hnear⟩ := hclose x hx
    refine ⟨g.basedMinimizingRayOfEdist ray hzero hmin, ?_⟩
    rw [g.rayExtension_basedMinimizingRayOfEdist ray hzero hmin dist_nonneg]
    exact hnear
  obtain ⟨L₀, hL₀, hrel⟩ :=
    exists_sphereLinkRelation_approximation hcomparison hdensity hε
  obtain ⟨γ⟩ := g.nonempty_basedMinimizingRays hc p
  refine ⟨L₀, hL₀, ?_⟩
  intro L hL
  obtain ⟨hsource, hlink, hdist⟩ := hrel L hL
  obtain ⟨x, _⟩ := hlink (asymptoticLinkProjection hcomparison γ)
  exact ⟨⟨x⟩, hsource, hlink, hdist⟩

end PoincareConjecture.RiemannianMetric
