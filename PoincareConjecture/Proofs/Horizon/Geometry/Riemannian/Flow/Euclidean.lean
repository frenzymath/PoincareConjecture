import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.Gauss.SquaredRadius
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.RadialConjugacy
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.RadialExtension

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [PreconnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem exists_diffeomorph_of_centered_radial_flow
    (g : RiemannianMetric n M) (p : M)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (hpotential : f =ᶠ[𝓝 p] (fun y => (g.edist y p).toReal ^ 2))
    {Y : (y : M) → TangentSpace (𝓡 n) y}
    (hY : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% Y))
    (hfield : ∀ᶠ y in 𝓝 p, Y y = (1 / 2 : ℝ) • g.gradient f y)
    {Φ : ℝ → M → M} (hzero : ∀ x, Φ 0 x = x)
    (horbit : ∀ x, IsMIntegralCurve (I := 𝓡 n) (fun t => Φ t x) Y)
    (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (Function.uncurry Φ))
    (hradius : ∀ x, x ≠ p → ∀ r : ℝ, 0 < r →
      ∃ t : ℝ, (g.edist p (Φ t x)).toReal = r) :
    ∃ d : Diffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞,
      d 0 = p := by
  let := g.toMetricSpace
  obtain ⟨e, r, hr, he0, hsource, he, hei, hfieldchart⟩ :=
    g.exists_radial_chart_of_squared_distance_gradient p hf hpotential hfield
  have hlocal := Poincare.Manifold.flow_eq_exp_smul_of_radial_field hY hzero horbit
    (he.mono hsource) hfieldchart
  have h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ e.source :=
    hsource (Metric.mem_ball_self hr)
  have hU : e '' Metric.ball 0 r ∈ 𝓝 p := by
    simpa only [he0] using e.image_mem_nhds h0 (Metric.ball_mem_nhds _ hr)
  obtain ⟨a, ha, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hhit (x : M) : ∃ t : ℝ, Φ t x ∈ e '' Metric.ball 0 r := by
    by_cases hxp : x = p
    · refine ⟨0, ?_⟩
      rw [hzero, hxp]
      exact ⟨0, Metric.mem_ball_self hr, he0⟩
    · obtain ⟨t, ht⟩ := hradius x hxp (a / 2) (half_pos ha)
      refine ⟨t, hball ?_⟩
      change dist (Φ t x) p < a
      rw [dist_comm, g.toMetricSpace_dist, ht]
      exact half_lt_self ha
  obtain ⟨d, hd⟩ := Poincare.Manifold.exists_diffeomorph_of_local_radial_flow
    Φ hs hzero hadd e he hei hr hsource hlocal hhit
  exact ⟨d, (hd 0 (Metric.mem_ball_self hr)).trans he0⟩

end PoincareConjecture.RiemannianMetric
