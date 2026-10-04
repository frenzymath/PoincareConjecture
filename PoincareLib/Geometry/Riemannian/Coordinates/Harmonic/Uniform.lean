import PoincareLib.Geometry.Riemannian.Coordinates.Harmonic.Composition
import PoincareLib.Geometry.Riemannian.Coordinates.Harmonic.Exponential
import PoincareLib.Geometry.Riemannian.Coordinates.Harmonic.Radius

/-!
# Uniform harmonic coordinate lifts

This file records the higher-dimensional output of the harmonic-radius
construction. The constants occur outside the manifold quantifiers, so the
interface cannot hide a geometry-dependent radius or an assumed harmonic
coordinate certificate. The geometric lift is constructed from completeness
and sectional curvature. `Harmonic.Radius` supplies the constructed weak
replacements, smooth inverse coordinates, and uniform coefficient estimates.

Reference: Chow--Chu--Glickenstein--Guenther--Isenberg--Ivey--Knopf--Lu--Luo--Ni,
Part III, Proposition 26.49, Step 3, equations (26.146)--(26.150), printed
pp. 383--384 (PDF pp. 404--405).
-/

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareMT.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Uniform harmonic coordinates from completeness and bounded sectional
curvature. Constants are selected before the manifold and no injectivity or
harmonic-coordinate premise is an input. -/
theorem exists_uniform_harmonic_lift
    (hn : 2 ≤ n) {K : ℝ} (hK : 0 < K) :
    ∃ r C H : ℝ, 0 < r ∧ 1 ≤ C ∧ 0 < H ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
        [IsManifold (𝓡 n) ∞ M] [T3Space M]
        (g : RiemannianMetric n M) (D : LeviCivitaData g),
        MetricComplete g →
        (∀ x (v w : TangentSpace (𝓡 n) x),
          |D.sectionalCurvature x v w| ≤ K) →
        ∀ p : M, Nonempty (UniformHarmonicLift g p r C H) := by
  obtain ⟨R, hR, hradial⟩ := exists_uniform_elliptic_radial_lift (n := n) hK.le
  obtain ⟨r, C, H, hr, hC, hH, hharmonic⟩ := exists_uniform_harmonic_radius hn hR
    (show 0 ≤ 4 * (n : ℝ) ^ 2 * K by positivity)
  refine ⟨r, C, H, hr, hC, hH, ?_⟩
  intro M _ _ _ _ g D hcomplete hsec p
  obtain ⟨e, h, D', he, he0, _, hpullback, hbound, hgauss, hcurv, _⟩ :=
    hradial g D hcomplete hsec p
  obtain ⟨F, hmap⟩ := hharmonic h D' hbound hgauss hcurv
  exact ⟨F.comp hr (lt_of_lt_of_le zero_lt_one hC) g Metric.isOpen_ball
    (he.mono (Metric.ball_subset_ball (by linarith))) he0 hpullback hmap⟩

end PoincareMT.RiemannianMetric
