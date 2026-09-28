import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.FiniteOrder.Metric
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.PullbackMetricJets









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem exists_uniform_pullback_metric_jet_bound
    (n m : ℕ) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R)
    (C : ℕ → ℝ) (hC : ∀ l, 0 ≤ C l) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ {M : Type*} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        (g : RiemannianMetric n M) (D : LeviCivitaData g)
        (e : EuclideanSpace ℝ (Fin n) → M),
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (ball 0 R) →
      (∀ x ∈ ball 0 R, (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible) →
      (∀ v w, g.pullbackCoefficients e 0 v w = inner ℝ v w) →
      (∀ x ∈ ball 0 R, ∀ w, g.pullbackCoefficients e x x w = inner ℝ x w) →
      (∀ l ≤ m, ∀ x ∈ ball 0 R, D.curvatureDerivativeNorm l (e x) ≤ C l) →
      ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) ρ,
        ‖iteratedFDeriv ℝ m (g.pullbackCoefficients e) x‖ ≤ B := by
  let r := (ρ + R) / 2
  let s := (r + R) / 2
  have hρr : ρ < r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r]; linarith
  have hr : 0 < r := hρ.trans hρr
  have hrs : r < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  obtain ⟨B, hB, hbound⟩ := exists_uniform_geodesic_coordinate_metric_jet_bound n m r C hC
  refine ⟨B, hB, ?_⟩
  intro M _ _ _ g D e he hi h0 hgauss hcurv
  have hcoeff : ContDiffOn ℝ ∞ (g.pullbackCoefficients e) (ball 0 R) :=
    fun x hx => (g.contDiffAt_pullbackCoefficients
      (he.contMDiffAt (isOpen_ball.mem_nhds hx))).contDiffWithinAt
  obtain ⟨gE, DE, heq, hG⟩ := exists_gauss_metric_extension hr hrs hsR
    (g.pullbackCoefficients e) hcoeff (fun x _ v w => g.symm (e x) _ _)
    (fun x hx v hv => by
      apply g.pos (e x)
      intro hz
      apply hv
      apply (hi x hx).injective
      rw [map_zero]
      convert! hz using 1) hgauss
  have hmetric (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ ball 0 r) (v w) :
      gE.inner x v w = g.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
        (mfderiv (𝓡 n) (𝓡 n) e x w) :=
    congrArg (fun A => A v w) (heq x (ball_subset_closedBall hx))
  have he' := he.mono (ball_subset_ball hrR.le)
  have hi' := fun x hx => hi x (ball_subset_ball hrR.le hx)
  have hcurv' (l : ℕ) (hl : l ≤ m) (x : EuclideanSpace ℝ (Fin n))
      (hx : x ∈ ball 0 r) : DE.curvatureDerivativeNorm l x ≤ C l := by
    rw [DE.curvatureDerivativeNorm_eq_pullback D isOpen_ball he' hi' hmetric l hx]
    exact hcurv l hl x (ball_subset_ball hrR.le hx)
  have hzero (v w : EuclideanSpace ℝ (Fin n)) : gE.inner 0 v w = inner ℝ v w := by
    have h := congrArg (fun A => A v w) (heq 0 (mem_closedBall_self hr.le))
    exact h.trans (h0 v w)
  have hgeo (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
      christoffelBilinear gE.euclideanCoefficients (t • x) x x = 0 :=
    christoffelBilinear_radial_eq_zero_of_gauss
      (contDiff_iff_contDiffAt.mpr gE.contDiffAt_euclideanCoefficients)
      gE.inner_isInvertible gE.symm hG x t
  intro x hx
  have hxr : x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) r :=
    lt_of_le_of_lt hx hρr
  have hgerm : gE.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients e := by
    filter_upwards [isOpen_ball.mem_nhds hxr] with y hy
    exact heq y (ball_subset_closedBall hy)
  rw [← (hgerm.iteratedFDeriv (𝕜 := ℝ) m).self_of_nhds]
  exact hbound gE DE hzero hgeo hcurv' x hxr

end PoincareConjecture.CoordinateExponential
