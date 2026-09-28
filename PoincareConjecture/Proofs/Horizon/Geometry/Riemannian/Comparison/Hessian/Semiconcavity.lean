import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Geodesic
import PoincareConjecture.Proofs.Horizon.Analysis.Convex.UpperSupport
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem distance_sub_quadratic_concave_of_annulus
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ y : M, ∀ u v : TangentSpace (𝓡 n) y,
      -K ≤ D.sectionalCurvature y u v)
    (p : M) {r R a b : ℝ} (hr : 0 < r) {γ : ℝ → M}
    (hγ : g.IsGeodesicOn γ (Icc a b))
    (hspeed : ∀ t ∈ Icc a b,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1)
    (hannulus : ∀ t ∈ Icc a b,
      r ≤ (g.edist p (γ t)).toReal ∧ (g.edist p (γ t)).toReal ≤ R) :
    ConcaveOn ℝ (Icc a b)
      (fun t => (g.edist p (γ t)).toReal - (2 / (3 * r) + K * R / 8) * t ^ 2) := by
  have hγcont : ContinuousOn γ (Icc a b) :=
    fun t ht => (hγ.contMDiffAt ht).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (fun t => (g.edist p (γ t)).toReal) (Icc a b) :=
    (g.continuous_toReal_edist p).comp_continuousOn hγcont
  apply Poincare.Analysis.concaveOn_sub_quadratic_of_approximate_upper_support hcont
  intro t ht ε hε
  have htcc : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  obtain ⟨hlo, hhi⟩ := hannulus t htcc
  have hpx : p ≠ γ t := by
    intro hp
    rw [← hp] at hlo
    simp only [edist, Manifold.riemannianEDist_self, ENNReal.toReal_zero] at hlo
    linarith
  obtain ⟨U, rho, hU, htU, hrho, htouch, hmajor, _, hbound⟩ :=
    g.exists_distance_hessian_upper_support D hcomplete hK hsec p (γ t) hpx
  have hγt := Conjugate.Realization.contMDiffAt_of_isGeodesicOn hγ htcc
  have hrhot := hrho.contMDiffAt (hU.mem_nhds htU)
  refine ⟨rho ∘ γ,
    (contMDiffAt_iff_contDiffAt.mp (hrhot.comp t hγt)).of_le (by norm_cast),
    htouch, ?_, ?_⟩
  · filter_upwards [hγt.continuousAt.preimage_mem_nhds (hU.mem_nhds htU)] with s hs
    exact hmajor (γ s) hs
  · rw [(D.hasDerivAt_deriv_comp_geodesic_of_contMDiffOn hU hrho hγ htcc htU).deriv]
    have hunit : g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1 := Real.sqrt_eq_one.mp (hspeed t htcc)
    have h := hbound (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
    rw [hunit, mul_one] at h
    have hinv : 4 / (3 * (g.edist p (γ t)).toReal) ≤ 4 / (3 * r) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_left hlo (by norm_num))
    have hcurv : K * (g.edist p (γ t)).toReal / 4 ≤ K * R / 4 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hhi hK) (by norm_num)
    have heq : 2 * (2 / (3 * r) + K * R / 8) = 4 / (3 * r) + K * R / 4 := by
      ring
    rw [heq]
    linarith




theorem exists_distance_semiconcave_neighborhood
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) {K : ℝ} (hK : 0 ≤ K)
    (hsec : ∀ y : M, ∀ u v : TangentSpace (𝓡 n) y,
      -K ≤ D.sectionalCurvature y u v)
    (p x : M) (hpx : p ≠ x) :
    ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ p ∉ U ∧
      ∀ (γ : ℝ → M) (a b : ℝ),
        g.IsGeodesicOn γ (Icc a b) →
        (∀ t ∈ Icc a b,
          g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1) →
        (∀ t ∈ Icc a b, γ t ∈ U) →
        ConcaveOn ℝ (Icc a b)
          (fun t => (g.edist p (γ t)).toReal -
            (4 / (3 * (g.edist p x).toReal) +
              3 * K * (g.edist p x).toReal / 16) * t ^ 2) := by
  have hdpos : 0 < g.edist p x := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
    exact edist_pos.mpr hpx
  have hd : 0 < (g.edist p x).toReal :=
    ENNReal.toReal_pos hdpos.ne' (g.edist_ne_top p x)
  let d := (g.edist p x).toReal
  let U := {y : M | d / 2 < (g.edist p y).toReal ∧ (g.edist p y).toReal < 3 * d / 2}
  have hU : IsOpen U :=
    (isOpen_lt continuous_const (g.continuous_toReal_edist p)).inter
      (isOpen_lt (g.continuous_toReal_edist p) continuous_const)
  refine ⟨U, hU, ?_, ?_, ?_⟩
  · change d / 2 < d ∧ d < 3 * d / 2
    constructor <;> dsimp [d] <;> linarith
  · intro hpU
    have h := hpU.1
    simp only [edist, Manifold.riemannianEDist_self, ENNReal.toReal_zero] at h
    dsimp [d] at h
    linarith
  · intro γ a b hγ hspeed hsub
    have h := g.distance_sub_quadratic_concave_of_annulus D hcomplete hK hsec p
      (show 0 < d / 2 by dsimp [d]; positivity) hγ hspeed
      (fun t ht => ⟨(hsub t ht).1.le, (hsub t ht).2.le⟩)
    convert h using 1
    ext t
    dsimp [d]
    ring

end PoincareConjecture.RiemannianMetric
