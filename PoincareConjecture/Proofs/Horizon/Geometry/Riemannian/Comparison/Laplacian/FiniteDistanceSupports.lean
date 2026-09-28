import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Support
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.TailSupport

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {m : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
  [IsManifold (𝓡 (m + 1)) ∞ M]

private theorem toReal_edist_triangle_of_finite
    (g : RiemannianMetric (m + 1) M) (p q y : M)
    (hpq : g.edist p q ≠ ⊤) (hqy : g.edist q y ≠ ⊤) :
    (g.edist p y).toReal ≤ (g.edist p q).toReal + (g.edist q y).toReal := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 (m + 1)) : M → Type _) := ⟨g.toRiemannianMetric⟩
  have htriangle := Manifold.riemannianEDist_triangle
    (I := 𝓡 (m + 1)) (x := p) (y := q) (z := y)
  change g.edist p y ≤ g.edist p q + g.edist q y at htriangle
  rw [← ENNReal.toReal_add hpq hqy]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hpq, hqy⟩) htriangle

theorem inverse_branch_distance_majorant_of_finite
    (g : RiemannianMetric (m + 1) M) (p q : M)
    {e : EuclideanSpace ℝ (Fin (m + 1)) → M} {R : ℝ}
    (hbound : ∀ w ∈ Metric.ball 0 R,
      g.edist q (e w) ≤ ENNReal.ofReal ‖w‖)
    (B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (m + 1))) M)
    (hsource : B.source ⊆ Metric.ball 0 R) (heB : EqOn e B B.source)
    {left : ℝ} (hleft : (g.edist p q).toReal = left)
    (hfinite : g.edist p q ≠ ⊤)
    {y : M} (hy : y ∈ B.target) :
    (g.edist p y).toReal ≤ left + ‖B.symm y‖ := by
  have hb := hbound (B.symm y) (hsource (B.map_target hy))
  rw [heB (B.map_target hy), B.right_inv hy] at hb
  have hqy : g.edist q y ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hb
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal (norm_nonneg _)] at hreal
  have htriangle := toReal_edist_triangle_of_finite g p q y hfinite hqy
  rw [hleft] at htriangle
  linarith

theorem inverse_branch_touches_distance_of_finite
    (g : RiemannianMetric (m + 1) M) {p x : M}
    {e : EuclideanSpace ℝ (Fin (m + 1)) → M}
    (B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (m + 1))) M)
    (heB : EqOn e B B.source) {v : EuclideanSpace ℝ (Fin (m + 1))}
    (hv : v ∈ B.source) (hx : e v = x) {left : ℝ}
    (hsplit : left + ‖v‖ = (g.edist p x).toReal) :
    left + ‖B.symm x‖ = (g.edist p x).toReal := by
  have hxB : B v = x := (heB hv).symm.trans hx
  rw [← hxB, B.left_inv hv]
  exact hxB ▸ hsplit

theorem upper_support_of_inverse_branch_of_finite
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g) (p q x : M)
    {e : EuclideanSpace ℝ (Fin (m + 1)) → M} {R k : ℝ}
    (hbound : ∀ w ∈ Metric.ball 0 R,
      g.edist q (e w) ≤ ENNReal.ofReal ‖w‖)
    (B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin (m + 1))) M)
    (hsource : B.source ⊆ Metric.ball 0 R) (heB : EqOn e B B.source)
    (hB : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ B B.source)
    (hBi : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ B.symm B.target)
    (hzero : ∀ y ∈ B.target, B.symm y ≠ 0)
    {v : EuclideanSpace ℝ (Fin (m + 1))} (hv : v ∈ B.source) (hx : e v = x)
    (hsplit : (g.edist p q).toReal + ‖v‖ = (g.edist p x).toReal)
    (hfinite : g.edist p q ≠ ⊤)
    (hhalf : (g.edist p x).toReal / 2 ≤ ‖v‖)
    (hgauss : ∀ w : EuclideanSpace ℝ (Fin (m + 1)),
      g.inner (e v) (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e v v)
        (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) e v w) = inner ℝ v w)
    (hlap : D.laplacian (fun y => ‖B.symm y‖) x ≤
      (m : ℝ) / ‖v‖ + (m : ℝ) * k) :
    ∃ (U : Set M) (rho : M → ℝ), IsOpen U ∧ x ∈ U ∧
      ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞ rho U ∧
      rho x = (g.edist p x).toReal ∧
      (∀ y ∈ U, (g.edist p y).toReal ≤ rho y) ∧
      g.inner x (D.gradient rho x) (D.gradient rho x) = 1 ∧
      D.laplacian rho x ≤ 2 * (m : ℝ) / (g.edist p x).toReal + (m : ℝ) * k := by
  subst x
  have hxB : B v = e v := (heB hv).symm
  have hxmem : e v ∈ B.target := hxB ▸ B.map_source hv
  have hrad : ContMDiffOn (𝓡 (m + 1)) 𝓘(ℝ, ℝ) ∞
      (fun y => ‖B.symm y‖) B.target :=
    fun y hy => (smooth_inverse_branch_radius B hBi hy (hzero y hy)).contMDiffWithinAt
  have hradx := hrad.contMDiffAt (B.open_target.mem_nhds hxmem)
  have hv0 : v ≠ 0 := by
    simpa only [B.left_inv hv] using hzero (B v) (B.map_source hv)
  have hr : 0 < (g.edist p (e v)).toReal := by
    rw [← hsplit]
    exact add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg (norm_pos_iff.mpr hv0)
  refine ⟨B.target, (fun y => (g.edist p q).toReal + ‖B.symm y‖),
    B.open_target, hxmem, contMDiffOn_const.add hrad,
    g.inverse_branch_touches_distance_of_finite B heB hv rfl hsplit, ?_, ?_, ?_⟩
  · intro y hy
    exact g.inverse_branch_distance_majorant_of_finite p q hbound B hsource heB
      rfl hfinite hy
  · rw [D.gradient_const_add_at (hradx.mdifferentiableAt (by simp))]
    exact g.inner_gradient_inverse_branch D B heB hB hBi hv hv0 hgauss
  · rw [D.laplacian_const_add_at hradx]
    exact hlap.trans (radius_comparison_of_half_le (Nat.cast_nonneg m) hr hhalf)

theorem upper_support_of_regular_minimizing_tail_of_finite
    (g : RiemannianMetric (m + 1) M) (D : LeviCivitaData g) (hm : 0 < m)
    (p q x : M) {e : EuclideanSpace ℝ (Fin (m + 1)) → M} {R k : ℝ}
    (he : ContMDiffOn (𝓡 (m + 1)) (𝓡 (m + 1)) ∞ e (Metric.ball 0 R))
    (hmetric : ∀ a b, g.pullbackCoefficients e 0 a b = inner ℝ a b)
    (hgeo : ∀ w ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun s : ℝ => e (s • w)) {s | s • w ∈ Metric.ball 0 R})
    (hbound : ∀ w ∈ Metric.ball 0 R,
      g.edist q (e w) ≤ ENNReal.ofReal ‖w‖)
    (hk : 0 ≤ k)
    (hRic : ∀ y : M, ∀ w : TangentSpace (𝓡 (m + 1)) y,
      -(m : ℝ) * k ^ 2 * g.inner y w w ≤ D.ricci y w w)
    {v : EuclideanSpace ℝ (Fin (m + 1))} (hv : v ∈ Metric.ball 0 R)
    (hv0 : v ≠ 0) (hx : e v = x)
    (hsplit : (g.edist p q).toReal + ‖v‖ = (g.edist p x).toReal)
    (hfinite : g.edist p q ≠ ⊤)
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
  exact g.upper_support_of_inverse_branch_of_finite D p q x hbound B hBU heB hB hBi
    hzero hvB hx hsplit hfinite hhalf (hgauss v hv) hlap

end PoincareConjecture.RiemannianMetric
