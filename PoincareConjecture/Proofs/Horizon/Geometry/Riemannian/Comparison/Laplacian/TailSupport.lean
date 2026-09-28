import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.RegularRay
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Support
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.RadialGauss







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]

theorem upper_support_of_regular_minimizing_tail
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g) (hm : 0 < m)
    (p q x : M) {e : EuclideanSpace ℝ (Fin (m + 1)) → M} {R k : ℝ}
    (he : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ e (Metric.ball 0 R))
    (hmetric : ∀ a b, g.pullbackCoefficients e 0 a b = inner ℝ a b)
    (hgeo : ∀ w ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun s : ℝ => e (s • w)) {s | s • w ∈ Metric.ball 0 R})
    (hbound : ∀ w ∈ Metric.ball 0 R, g.edist q (e w) ≤ ENNReal.ofReal ‖w‖)
    (hk : 0 ≤ k)
    (hRic : ∀ y : M, ∀ w : TangentSpace (𝓡 (m + 1)) y,
      -(m : ℝ) * k ^ 2 * g.inner y w w ≤ D.ricci y w w)
    {v : EuclideanSpace ℝ (Fin (m + 1))} (hv : v ∈ Metric.ball 0 R)
    (hv0 : v ≠ 0) (hx : e v = x)
    (hsplit : (g.edist p q).toReal + ‖v‖ = (g.edist p x).toReal)
    (hhalf : (g.edist p x).toReal / 2 ≤ ‖v‖)
    (hi : ∀ s ∈ Icc (0 : ℝ) 1,
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (s • v)).IsInvertible) :
    ∃ (U : Set M) (rho : M → ℝ), IsOpen U ∧ x ∈ U ∧
      ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ rho U ∧
      rho x = (g.edist p x).toReal ∧
      (∀ y ∈ U, (g.edist p y).toReal ≤ rho y) ∧
      g.inner x (D.gradient rho x) (D.gradient rho x) = 1 ∧
      D.laplacian rho x ≤ 2 * (m : ℝ) / (g.edist p x).toReal + (m : ℝ) * k := by
  let θ := ‖v‖⁻¹ • v
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hθ : ‖θ‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']
  have hnorm (s : ℝ) (hs : 0 ≤ s) : ‖s • θ‖ = s := by
    rw [norm_smul, Real.norm_of_nonneg hs, hθ, mul_one]
  have hR : ‖v‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  have hsub : ∀ s ∈ Icc 0 ‖v‖, s • θ ∈ Metric.ball 0 R := by
    intro s hs
    rw [Metric.mem_ball, dist_zero_right, hnorm s hs.1]
    exact hs.2.trans_lt hR
  have hi' : ∀ s ∈ Icc 0 ‖v‖,
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e (s • θ)).IsInvertible := by
    intro s hs
    have hst : s / ‖v‖ ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hs.1 hn.le, (div_le_one hn).mpr hs.2⟩
    rw [show s • θ = (s / ‖v‖) • v by simp only [θ, smul_smul, div_eq_mul_inv]]
    exact hi (s / ‖v‖) hst
  obtain ⟨b, hnb, hbsub, hbi⟩ := exists_regular_radial_extension
    Metric.isOpen_ball he θ hn.le hsub hi'
  obtain ⟨B, hvB, hBU, heB, hB, hBi, hzero, _⟩ :=
    exists_smooth_radial_inverse_branch Metric.isOpen_ball he hv hv0
      (by have h := hi 1 (by simp); rw [one_smul] at h; exact h)
  have htθ : ‖v‖ • θ = v := by
    dsimp only [θ]
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have hgauss := g.radial_gauss_identity D he hmetric hgeo
  have hgaussNear : ∀ᶠ y in 𝓝 (‖v‖ • θ), ∀ w,
      g.inner (e y) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e y y)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e y w) = inner ℝ y w := by
    rw [htθ]
    filter_upwards [Metric.isOpen_ball.mem_nhds hv] with y hy
    exact hgauss y hy
  have hlap := g.laplacian_inverse_branch_le_of_ricci D hm Metric.isOpen_ball
    (by simpa using hn.trans hR) he hgeo hmetric θ hθ (hn.trans hnb)
    ⟨hn, hnb⟩ hk hbsub (fun s hs => (hbi s hs).injective)
    (fun s _ w => hRic (e (s • θ)) w) B heB hB hBi
    (by simpa only [htθ] using hvB) hgaussNear
  rw [htθ, hx] at hlap
  exact g.upper_support_of_inverse_branch D p q x hbound B hBU heB hB hBi
    hzero hvB hx hsplit hhalf (hgauss v hv) hlap

end PoincareConjecture.RiemannianMetric
