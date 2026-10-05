import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Curvature.CurvatureJetNorm
import PoincareLib.Geometry.Riemannian.Coordinates.Exponential.JetBounds.CurvatureNaturality
import PoincareLib.Geometry.Riemannian.Coordinates.Harmonic.Perturbation

/-!
# The intrinsic curvature jet bound in arbitrary manifold charts

A local realization of the positive pullback coefficients reduces to
the universal Euclidean estimate. Equality as germs transfers every
coefficient jet, and geometric naturality transfers the full curvature
derivative norm. This is the interpolation estimate for the compact
restart approximations in Morgan-Tian Theorem 12.5, pp. 296-297.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- Pullback coefficients and tangent-model maps use dependent normed spaces.
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareMT.M34

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

set_option synthInstance.maxHeartbeats 100000 in
-- The local metric realization preserves all finite coefficient jets.
/-- A uniform elliptic finite-jet bound controls actual curvature in
every smooth locally invertible chart. The constant precedes the
manifold, metric, connection, chart, and point
(Theorem 12.5, pp. 296-297). -/
theorem curvatureDerivativeNorm_bound_of_pullback_jets
    (n m : ℕ) {a : ℝ} (ha : 0 < a) (H : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {M : Type*} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
      {g : RiemannianMetric n M} (D : LeviCivitaData g)
      {U : Set (EuclideanSpace ℝ (Fin n))}, IsOpen U →
      ∀ {e : EuclideanSpace ℝ (Fin n) → M}, ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U →
      (∀ y ∈ U, (mfderiv (𝓡 n) (𝓡 n) e y).IsInvertible) →
      ∀ {x : EuclideanSpace ℝ (Fin n)}, x ∈ U →
      (∀ j ≤ 2 + m, ‖iteratedFDeriv ℝ j (g.pullbackCoefficients e) x‖ ≤ H) →
      (∀ v, a * ‖v‖ ^ 2 ≤ g.pullbackCoefficients e x v v) →
      D.curvatureDerivativeNorm m (e x) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := curvatureDerivativeNorm_bound_of_coefficient_jets n m ha H
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ g D U hU e he hinv x hx hjets hell
  have hcoeff : ContDiffOn ℝ ∞ (g.pullbackCoefficients e) U := fun y hy =>
    (g.contDiffAt_pullbackCoefficients (he.contMDiffAt (hU.mem_nhds hy))).contDiffWithinAt
  obtain ⟨gE, DE, V, hV, hxV, hVU, heq⟩ := RiemannianMetric.exists_local_realization
    hU hx (g.pullbackCoefficients e) hcoeff (fun y _ u v => g.symm (e y) _ _)
    (fun y hy w hw => by
      apply g.pos (e y)
      intro hz
      apply hw
      apply (hinv y hy).injective
      rw [map_zero]
      convert! hz using 1)
  have hmetric (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ V) (u v) :
      gE.inner y u v = g.inner (e y)
        (mfderiv (𝓡 n) (𝓡 n) e y u) (mfderiv (𝓡 n) (𝓡 n) e y v) :=
    congrArg (fun B => B u v) (heq y hy)
  have hB : gE.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients e := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact heq y hy
  rw [← DE.curvatureDerivativeNorm_eq_pullback D hV (he.mono hVU)
    (fun y hy => hinv y (hVU hy)) hmetric m hxV]
  apply hbound gE DE x
  · intro j hj
    rw [(hB.iteratedFDeriv (𝕜 := ℝ) j).eq_of_nhds]
    exact hjets j hj
  · intro v
    rw [heq x hxV]
    exact hell v

end PoincareMT.M34
