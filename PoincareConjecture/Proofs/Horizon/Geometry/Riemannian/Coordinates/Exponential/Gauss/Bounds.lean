import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.Gauss.NormalizedChart

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_normalized_exponential_chart_bounds (g : RiemannianMetric n M)
    (p : M) {ε : ℝ} (hε : 0 < ε) :
    let B₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M, ∃ r : ℝ,
      0 < r ∧ Metric.ball 0 r ⊆ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      ∀ y ∈ Metric.ball 0 r,
        ‖g.pullbackCoefficients e y - B₀‖ < ε ∧
        ‖CoordinateExponential.christoffelBilinear (g.pullbackCoefficients e) y‖ < ε ∧
        ∀ v, (1 - ε) * ‖v‖ ^ 2 ≤ g.pullbackCoefficients e y v v ∧
          g.pullbackCoefficients e y v v ≤ (1 + ε) * ‖v‖ ^ 2 := by
  let B₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
  change ∃ e r, _
  obtain ⟨e, he0, hep, he, hei, _, hB0, hΓ0⟩ :=
    g.exists_normalized_exponential_chart_firstJet p
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hB := g.contDiffAt_pullbackCoefficients
    (he.contMDiffAt (e.open_source.mem_nhds he0))
  have hΓ := (CoordinateExponential.contDiffAt_christoffelBilinear hB
    (g.isInvertible_pullbackCoefficients (hD.mfderiv_injective he0))).continuousAt
  have hBnear : ∀ᶠ y in 𝓝 0,
      ‖g.pullbackCoefficients e y - B₀‖ < ε := by
    have h := hB.continuousAt.eventually (Metric.ball_mem_nhds _ hε)
    simpa only [Metric.mem_ball, dist_eq_norm, hB0, B₀] using h
  have hΓnear : ∀ᶠ y in 𝓝 0,
      ‖CoordinateExponential.christoffelBilinear (g.pullbackCoefficients e) y‖ < ε := by
    have h := hΓ.eventually (Metric.ball_mem_nhds _ hε)
    simpa only [Metric.mem_ball, dist_eq_norm, hΓ0, sub_zero] using h
  have hev : ∀ᶠ y in 𝓝 0, y ∈ e.source ∧
      ‖g.pullbackCoefficients e y - B₀‖ < ε ∧
      ‖CoordinateExponential.christoffelBilinear (g.pullbackCoefficients e) y‖ < ε := by
    filter_upwards [e.open_source.mem_nhds he0, hBnear, hΓnear] with y hy hBy hΓy
    exact ⟨hy, hBy, hΓy⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨e, r, hr, fun y hy => (hball hy).1, hep, he, hei, ?_⟩
  intro y hy
  refine ⟨(hball hy).2.1, (hball hy).2.2, ?_⟩
  intro v
  have hnorm := (g.pullbackCoefficients e y - B₀).le_opNorm₂ v v
  change |g.pullbackCoefficients e y v v - inner ℝ v v| ≤
    ‖g.pullbackCoefficients e y - B₀‖ * ‖v‖ * ‖v‖ at hnorm
  rw [real_inner_self_eq_norm_sq] at hnorm
  have herr : |g.pullbackCoefficients e y v v - ‖v‖ ^ 2| ≤ ε * ‖v‖ ^ 2 :=
    hnorm.trans (by nlinarith [(hball hy).2.1, sq_nonneg ‖v‖])
  constructor <;> nlinarith [abs_le.mp herr]

end PoincareConjecture.RiemannianMetric
