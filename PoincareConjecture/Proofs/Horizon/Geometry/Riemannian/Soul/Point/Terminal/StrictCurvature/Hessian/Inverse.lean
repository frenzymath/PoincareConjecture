import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.StrictCurvature.Hessian.Radial
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Inverse
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Divergence.Radial

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

open CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem hessian_inverse_radius_le_sub_endpoint_ball_curvature [T2Space M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hsec : D.NonnegativeSectionalCurvature)
    {e : EuclideanSpace ℝ (Fin n) → M} {R : ℝ}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hnorm : ∀ a b, g.pullbackCoefficients e 0 a b = inner ℝ a b)
    (hradial : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun r : ℝ => e (r • v))
        {r : ℝ | r • v ∈ Metric.ball 0 R})
    (B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (heB : EqOn e B B.source)
    (hB : ContMDiffOn (𝓡 n) (𝓡 n) ∞ B B.source)
    (hBi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ B.symm B.target)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ Metric.ball 0 R) (hvB : v ∈ B.source)
    (hv0 : v ≠ 0)
    (hmin : g.edist (e 0) (e v) = ENNReal.ofReal ‖v‖)
    {κ ρ : ℝ} (hρ : 0 ≤ ρ) (hρv : ρ ≤ ‖v‖)
    (hball : ∀ y, (g.edist y (e v)).toReal ≤ ρ → ∀ u z,
      κ * (g.inner y u u * g.inner y z z - (g.inner y u z) ^ 2) ≤
        D.curvatureTensor y u z u z)
    (w : TangentSpace (𝓡 n) (e v)) :
    D.hessian (fun y => ‖B.symm y‖) (e v) w w ≤
      (1 / ‖v‖ - κ * ‖v‖ * ((1 - (1 - ρ / ‖v‖) ^ 3) / 3)) *
        (g.inner (e v) w w - (mvfderiv (𝓡 n) (fun y => ‖B.symm y‖) (e v) w) ^ 2) := by
  have hD : B.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨hB.mdifferentiableOn (by simp), hBi.mdifferentiableOn (by simp)⟩
  have heq : e =ᶠ[𝓝 v] B :=
    Filter.eventuallyEq_of_mem (B.open_source.mem_nhds hvB) heB
  have hiB : (mfderiv (𝓡 n) (𝓡 n) B v).IsInvertible := ⟨hD.mfderiv hvB, rfl⟩
  have hi : (mfderiv (𝓡 n) (𝓡 n) e v).IsInvertible := by
    rw [heq.mfderiv_eq]
    exact hiB
  have hcoeff : g.pullbackCoefficients e =ᶠ[𝓝 v] g.pullbackCoefficients B := by
    filter_upwards [eventually_eventually_nhds.mpr heq] with y hy
    change e =ᶠ[𝓝 y] B at hy
    unfold pullbackCoefficients
    rw [hy.mfderiv_eq, hy.self_of_nhds]
  have hΓ : coordinateChristoffel (g.pullbackCoefficients e) v =
      coordinateChristoffel (g.pullbackCoefficients B) v := by
    funext a b
    simp only [coordinateChristoffel, hcoeff.self_of_nhds, hcoeff.fderiv_eq]
  have hgauss : ∀ᶠ y in 𝓝 v, ∀ z,
      g.pullbackCoefficients B y y z = inner ℝ y z := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hv, hcoeff] with y hy hcy z
    rw [← hcy]
    exact g.radial_gauss_identity D he hnorm hradial y hy z
  let z := (mfderiv (𝓡 n) (𝓡 n) e v).inverse w
  have hbound := Hessian.radial_pairing_le_sub_endpoint_ball_curvature
    g D hsec he hnorm hradial hv hv0 hi.bijective hmin hρ hρv hball z
  have hsq := g.hessian_inverse_radius_sq D B hB hBi hvB hv0 hgauss z
  rw [← heq.mfderiv_eq, ← heq.self_of_nhds, hi.self_apply_inverse] at hsq
  rw [hcoeff.self_of_nhds, hΓ] at hbound
  have hquad : g.pullbackCoefficients B v z z = g.inner (e v) w w := by
    rw [← hcoeff.self_of_nhds]
    change g.inner (e v) (mfderiv (𝓡 n) (𝓡 n) e v z)
      (mfderiv (𝓡 n) (𝓡 n) e v z) = _
    rw [hi.self_apply_inverse]
  rw [hquad] at hbound
  have hs := smooth_inverse_branch_radius B hBi (B.map_source hvB)
    (by simpa only [B.left_inv hvB] using hv0)
  rw [← heq.self_of_nhds] at hs
  have hmul := D.hessian_mul_at hs hs w w
  simp only [← sq, show B.symm (e v) = v by rw [heq.self_of_nhds, B.left_inv hvB]] at hmul
  have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hgrad := D.gradient_radial_coordinate B hB hBi hvB hv0
    (hgauss.self_of_nhds)
  have hwB : mfderiv (𝓡 n) (𝓡 n) B v z = w := by
    rw [← heq.mfderiv_eq]
    exact hi.self_apply_inverse w
  have hd : mvfderiv (𝓡 n) (fun y => ‖B.symm y‖) (e v) w =
      ‖v‖⁻¹ * inner ℝ v z := by
    rw [← D.inner_gradient, heq.self_of_nhds, hgrad]
    rw [← hwB]
    simp only [map_smul, smul_apply, smul_eq_mul]
    exact congrArg (fun a : ℝ => ‖v‖⁻¹ * a) (hgauss.self_of_nhds z)
  have hinner : inner ℝ v z =
      ‖v‖ * mvfderiv (𝓡 n) (fun y => ‖B.symm y‖) (e v) w := by
    rw [hd, ← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  rw [hinner] at hbound
  apply (mul_le_mul_iff_of_pos_right hr).mp
  have halgebra :
      ((1 / ‖v‖ - κ * ‖v‖ * ((1 - (1 - ρ / ‖v‖) ^ 3) / 3)) *
        (g.inner (e v) w w - (mvfderiv (𝓡 n) (fun y => ‖B.symm y‖) (e v) w) ^ 2)) * ‖v‖ =
      (g.inner (e v) w w - κ * (‖v‖ ^ 2 * g.inner (e v) w w -
        (‖v‖ * mvfderiv (𝓡 n) (fun y => ‖B.symm y‖) (e v) w) ^ 2) *
          ((1 - (1 - ρ / ‖v‖) ^ 3) / 3)) -
            (mvfderiv (𝓡 n) (fun y => ‖B.symm y‖) (e v) w) ^ 2 := by
    field_simp
    ring
  rw [halgebra]
  nlinarith only [hmul, hsq, hbound]

end PoincareConjecture.RiemannianMetric
