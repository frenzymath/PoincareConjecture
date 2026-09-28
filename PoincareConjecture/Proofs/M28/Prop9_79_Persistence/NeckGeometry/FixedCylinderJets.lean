import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckGeometry.CapturedCylinderJets
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderMetricBounds
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderFiniteJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Proofs.M28.NeckTransfer

open PoincareConjecture.M28.tube FiniteHessian

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem cylinderNeckCoefficients_unscale (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    g.pullbackCoefficients (cylinderNeckChart N q s) x =
      N.scale ^ 2 • cylinderNeckCoefficients N q s x := by
  have hcancel : N.scale ^ 2 * N.scale⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ N.scale_pos.ne', one_pow]
  ext v w
  change g.pullbackCoefficients (cylinderNeckChart N q s) x v w =
    N.scale ^ 2 * (N.scale⁻¹ ^ 2 *
      g.pullbackCoefficients (cylinderNeckChart N q s) x v w)
  rw [← mul_assoc, hcancel, one_mul]

theorem hasUniformJetBoundsAt_fixedCylinderCoordinates_fderiv
    (N : EpsilonNeck g) {ι : Type*}
    (q : ι → UnitTwoSphere) (s : ι → ℝ) (p : ι → M)
    (hs : ∀ i, s i ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hp : ∀ i, N.coordinate_map (q i, s i) ∈ (extChartAt (𝓡 3) (p i)).source)
    (n : ℕ) (hn : n + 1 ≤ ⌊N.epsilon⁻¹⌋₊)
    (hBj : HasUniformJetBoundsAt (n + 1)
      (fun i => g.pullbackCoefficients (extChartAt (𝓡 3) (p i)).symm)
      (fun i => (extChartAt (𝓡 3) (p i)) (N.coordinate_map (q i, s i))))
    {b : ℝ} (hb : 0 < b)
    (hBe : ∀ i v, b * ‖v‖ ^ 2 ≤
      g.pullbackCoefficients (extChartAt (𝓡 3) (p i)).symm
        ((extChartAt (𝓡 3) (p i)) (N.coordinate_map (q i, s i))) v v) :
    HasUniformJetBoundsAt (n + 1)
      (fun i => fderiv ℝ ((extChartAt (𝓡 3) (p i)) ∘ cylinderNeckChart N (q i) (s i)))
      (fun _ => 0) := by
  let : AddMonoid (SpacetimeBounds.MetricCoefficient 3) :=
    (inferInstance : NormedAddCommGroup (SpacetimeBounds.MetricCoefficient 3)).toAddMonoid
  let e := (Diffeomorph.refl (𝓡 3) M ∞).toPartialDiffeomorph
  have hj := hasUniformJetBoundsAt_cylinderNeckCoefficients (fun _ : ι => N)
    N.epsilon_pos (by linarith [N.epsilon_lt_half]) (fun _ => rfl) (n + 1) hn q s hs
  have hc (i : ι) : ContDiffAt ℝ ∞ (cylinderNeckCoefficients N (q i) (s i)) 0 :=
    (contDiffOn_cylinderNeckCoefficients N (q i) (s i)).contDiffAt
      ((isOpen_cylinderNeckChartDomain N (q i) (s i)).mem_nhds
        (zero_mem_cylinderNeckChartDomain N (q i) (hs i)))
  let L : SpacetimeBounds.MetricCoefficient 3 →L[ℝ] SpacetimeBounds.MetricCoefficient 3 :=
    N.scale ^ 2 • ContinuousLinearMap.id ℝ (SpacetimeBounds.MetricCoefficient 3)
  have hAj : HasUniformJetBoundsAt (n + 1)
      (fun i => g.pullbackCoefficients (cylinderNeckChart N (q i) (s i))) (fun _ => 0) := by
    apply (hj.clm hc L).congr_germ
    intro i
    filter_upwards [] with x
    exact (cylinderNeckCoefficients_unscale N (q i) (s i) x).symm
  have ha : 0 < N.scale ^ 2 * (1 - N.epsilon) :=
    mul_pos (sq_pos_of_pos N.scale_pos) (by linarith [N.epsilon_lt_half])
  have hAe (i : ι) (v : EuclideanSpace ℝ (Fin 3)) :
      (N.scale ^ 2 * (1 - N.epsilon)) * ‖v‖ ^ 2 ≤
        g.pullbackCoefficients (cylinderNeckChart N (q i) (s i)) 0 v v := by
    rw [cylinderNeckCoefficients_unscale]
    simpa only [smul_apply, smul_eq_mul, mul_assoc] using
      mul_le_mul_of_nonneg_left
        (cylinderNeckCoefficients_quadratic_bounds N (q i) (hs i) v).1 (sq_nonneg N.scale)
  have hB' : HasUniformJetBoundsAt (n + 1)
      (fun i => g.pullbackCoefficients (e ∘ (extChartAt (𝓡 3) (p i)).symm))
      (fun i => capturedCylinderCoordinates e N (q i) (s i) (p i) 0) := by
    change HasUniformJetBoundsAt (n + 1)
      (fun i => g.pullbackCoefficients (extChartAt (𝓡 3) (p i)).symm)
      (fun i => (extChartAt (𝓡 3) (p i)) (cylinderNeckChart N (q i) (s i) 0))
    simpa only [cylinderNeckChart_zero] using hBj
  have h := hasUniformJetBoundsAt_capturedCylinderCoordinates_fderiv
    (fun _ : ι => g) (fun _ => e) (fun _ => N) (fun _ _ _ => mem_univ _)
    q s p hs hp n hAj hB' ha hb hAe (fun i v => by
      change b * ‖v‖ ^ 2 ≤ g.pullbackCoefficients (extChartAt (𝓡 3) (p i)).symm
        ((extChartAt (𝓡 3) (p i)) (cylinderNeckChart N (q i) (s i) 0)) v v
      rw [cylinderNeckChart_zero]
      exact hBe i v)
  exact h

end PoincareConjecture.Proofs.M28.NeckTransfer
