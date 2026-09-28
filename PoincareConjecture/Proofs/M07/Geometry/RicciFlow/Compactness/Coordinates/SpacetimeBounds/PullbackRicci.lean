import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.SpatialRicci
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.LocalIsometryRicci
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CurvatureNaturality











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.LeviCivitaData

open CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem norm_fderiv_pullback_ricci_le (D : LeviCivitaData g)
    (hM04 : RicciFlowCurvatureTheory.{0})
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (hi : ∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    {a b K L : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hlower : ∀ w, a * ‖w‖ ^ 2 ≤ g.pullbackCoefficients e x w w)
    (hupper : ∀ w, g.pullbackCoefficients e x w w ≤ b * ‖w‖ ^ 2)
    (hcurv : D.curvatureDerivativeNorm 0 (e x) ≤ K)
    (hcurv' : D.curvatureDerivativeNorm 1 (e x) ≤ L)
    (u v : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ (fun y => D.ricci (e y)
      (mfderiv (𝓡 n) (𝓡 n) e y u) (mfderiv (𝓡 n) (𝓡 n) e y v)) x‖ ≤
      ((n : ℝ) * L * (Real.sqrt b) ^ 3 +
        (3 * (n : ℝ) * K * b / a) * ‖fderiv ℝ (g.pullbackCoefficients e) x‖) *
          ‖u‖ * ‖v‖ := by
  have hcoeff : ContDiffOn ℝ ∞ (g.pullbackCoefficients e) U := fun y hy =>
    (g.contDiffAt_pullbackCoefficients (he.contMDiffAt (hU.mem_nhds hy))).contDiffWithinAt
  obtain ⟨gE, DE, V, hV, hxV, hVU, heq⟩ := RiemannianMetric.exists_local_realization
    hU hx (g.pullbackCoefficients e) hcoeff (fun y _ u v => g.symm (e y) _ _)
    (fun y hy w hw => by
      apply g.pos (e y)
      intro hz
      apply hw
      apply (hi y hy).injective
      rw [map_zero]
      convert! hz using 1)
  have hmetric (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ V) (u v) :
      gE.inner y u v = g.inner (e y)
        (mfderiv (𝓡 n) (𝓡 n) e y u) (mfderiv (𝓡 n) (𝓡 n) e y v) :=
    congrArg (fun B => B u v) (heq y hy)
  have hB : gE.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients e := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact heq y hy
  have hRic : (fun y => DE.ricci y u v) =ᶠ[𝓝 x]
      (fun y => D.ricci (e y) (mfderiv (𝓡 n) (𝓡 n) e y u)
        (mfderiv (𝓡 n) (𝓡 n) e y v)) := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact DE.ricci_eq_of_local_isometry D hV (he.mono hVU) hmetric hy u v
  have hnorm (w : EuclideanSpace ℝ (Fin n)) : gE.tangentNorm x w ≤ Real.sqrt b * ‖w‖ := by
    have h := Real.sqrt_le_sqrt (hupper w)
    rw [Real.sqrt_mul hb, Real.sqrt_sq (norm_nonneg w)] at h
    change Real.sqrt (gE.euclideanCoefficients x w w) ≤ _
    rw [heq x hxV]
    exact h
  have hell (w : EuclideanSpace ℝ (Fin n)) : a * ‖w‖ ^ 2 ≤ gE.euclideanCoefficients x w w := by
    rw [heq x hxV]
    exact hlower w
  have hcurvE (m : ℕ) : DE.curvatureDerivativeNorm m x = D.curvatureDerivativeNorm m (e x) :=
    DE.curvatureDerivativeNorm_eq_pullback D hV (he.mono hVU)
      (fun y hy => hi y (hVU hy)) hmetric m hxV
  have hbound := DE.norm_fderiv_ricci_le
    (hM04.tensor_calculus n (EuclideanSpace ℝ (Fin n)) gE DE) x u v
    (Real.sqrt_nonneg b) (by positivity : 0 ≤ (3 / (2 * a)) * ‖fderiv ℝ gE.euclideanCoefficients x‖)
    hK hL hnorm (norm_christoffelBilinear_le_of_ellipticity _ x ha hell)
    (by rw [hcurvE]; exact hcurv) (by rw [hcurvE]; exact hcurv')
  rw [hRic.fderiv_eq, hB.fderiv_eq, Real.sq_sqrt hb] at hbound
  convert hbound using 1
  ring

end PoincareConjecture.LeviCivitaData
