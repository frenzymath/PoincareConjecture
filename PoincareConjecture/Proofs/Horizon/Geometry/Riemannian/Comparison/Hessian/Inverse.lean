import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Locality
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Radial
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Inverse


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



theorem hessian_inverse_radius_sq
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (hB : ContMDiffOn (𝓡 n) (𝓡 n) ∞ B B.source)
    (hBi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ B.symm B.target)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ B.source) (hx0 : x ≠ 0)
    (hgauss : ∀ᶠ y in 𝓝 x, ∀ w,
      g.pullbackCoefficients B y y w = inner ℝ y w)
    (w : EuclideanSpace ℝ (Fin n)) :
    D.hessian (fun y => ‖B.symm y‖ ^ 2) (B x)
        (mfderiv (𝓡 n) (𝓡 n) B x w) (mfderiv (𝓡 n) (𝓡 n) B x w) =
      2 * g.pullbackCoefficients B x
        (w + coordinateChristoffel (g.pullbackCoefficients B) x x w) w := by
  have hs := smooth_inverse_branch_radius B hBi (B.map_source hx)
    (by simpa only [B.left_inv hx] using hx0)
  have heq : ((fun y => ‖B.symm y‖ ^ 2) ∘ B) =ᶠ[𝓝 x]
      (fun y => ‖y‖ ^ 2) := by
    filter_upwards [B.open_source.mem_nhds hx] with y hy
    simp only [Function.comp_apply, B.left_inv hy]
  rw [D.hessian_in_smooth_local_parametrization B hB hBi hx (hs.pow 2) w w,
    heq.fderiv.fderiv_eq, heq.fderiv_eq]
  have hsecond : fderiv ℝ (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2)) x =
      2 • innerSL ℝ := by
    rw [fderiv_norm_sq]
    simpa only [two_smul] using
      ((innerSL ℝ (E := EuclideanSpace ℝ (Fin n))).hasFDerivAt.add
        (innerSL ℝ).hasFDerivAt).fderiv
  rw [hsecond, fderiv_norm_sq_apply]
  simp only [two_smul, add_apply, innerSL_apply_apply, christoffelBilinear_apply]
  change (inner ℝ w w + inner ℝ w w) - _ = _
  have hD : B.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨hB.mdifferentiableOn (by simp), hBi.mdifferentiableOn (by simp)⟩
  have hp := radial_hessian_pairing_of_gauss
    ((g.contDiffAt_pullbackCoefficients
      (hB.contMDiffAt (B.open_source.mem_nhds hx))).differentiableAt (by simp))
    (g.isInvertible_pullbackCoefficients (hD.mfderiv_injective hx))
    (Eventually.of_forall fun _ a b => g.symm _ _ _) hgauss w
  linarith



theorem hessian_inverse_radius_le_of_sectional_lower_bound [T2Space M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ x : M, ∀ u v : TangentSpace (𝓡 n) x,
      -K ≤ D.sectionalCurvature x u v)
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
    (w : TangentSpace (𝓡 n) (e v)) :
    D.hessian (fun y => ‖B.symm y‖) (e v) w w ≤
      (1 / ‖v‖ + K * ‖v‖ / 3) * g.inner (e v) w w := by
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
  have hbound := Hessian.radial_pairing_le_of_sectional_lower_bound
    g D hK hsec he hnorm hradial hv hv0 hi.bijective hmin z
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
  have htarget : (1 / ‖v‖ + K * ‖v‖ / 3) * ‖v‖ = 1 + K * ‖v‖ ^ 2 / 3 := by
    field_simp
  apply (mul_le_mul_iff_of_pos_right hr).mp
  rw [mul_assoc, mul_comm (g.inner (e v) w w) ‖v‖, ← mul_assoc, htarget]
  nlinarith [sq_nonneg (mvfderiv (𝓡 n) (fun y => ‖B.symm y‖) (e v) w)]

end PoincareConjecture.RiemannianMetric
