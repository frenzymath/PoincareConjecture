import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Jets.Reparametrization
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Jets.Ellipticity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Acceleration.Estimate
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Acceleration.NeckChart








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_axial_hessian_bound :
    ∃ K : ℝ, ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
      {x : M}, x ∈ N.carrier → ∀ v : TangentSpace (𝓡 3) x,
      g.tangentNorm x v = 1 →
      |N.connection.hessian N.axialCoordinate x v v| ≤ K * N.epsilon / N.scale ^ 2 := by
  let e : RoundCylinderCoordinates ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (RiemannianMetric.lineModelEquiv 2).trans finSuccModelEquiv
  let a : ℝ := (2 * (max 1 ‖e.toContinuousLinearMap‖) ^ 2)⁻¹
  let d : ℝ := 216 * ‖e.symm.toContinuousLinearMap‖ ^ 3
  have hA : 0 < max 1 ‖e.toContinuousLinearMap‖ :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have ha : 0 < a := by dsimp [a]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  refine ⟨3 * ‖axialLinearCoordinate‖ * d / (2 * a ^ 2), ?_⟩
  intro M _ _ _ _ _ _ _ g N x hx u hu
  let q := (N.coordinate_inverse x).1
  let s := (N.coordinate_inverse x).2
  have hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := (N.coordinate_inverse_mem x hx).2
  let p := e (0, s)
  let B := N.euclideanNeckChart q
  have hp : p ∈ B.source := N.euclideanNeckChart_center_source q hs
  have hpx : B p = x := by
    rw [show B p = N.coordinate_map (q, s) from N.euclideanNeckChart_center_apply q hs]
    exact N.coordinate_map_coordinate_inverse hx
  have hB : B.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨(N.euclideanNeckChart_smooth q).mdifferentiableOn (by simp),
      (N.euclideanNeckChart_symm_smooth q).mdifferentiableOn (by simp)⟩
  have hinv : (mfderiv (𝓡 3) (𝓡 3) B p).IsInvertible := ⟨hB.mfderiv hp, rfl⟩
  obtain ⟨v, hv⟩ := hinv.surjective u
  have hchart : (B : EuclideanSpace ℝ (Fin 3) → M) =
      N.centeredParametrization q ∘ e.symm := rfl
  have hlower (w : RoundCylinderCoordinates) :
      (N.scale ^ 2 / 2) * ‖w‖ ^ 2 ≤
        g.parametrizedCoefficients (N.centeredParametrization q) (0, s) w w := by
    have h := N.normalizedCenteredCoefficients_lower q hs w
    have hhalf : (1 / 2 : ℝ) * ‖w‖ ^ 2 ≤
        N.normalizedCenteredCoefficients q (0, s) w w :=
      (mul_le_mul_of_nonneg_right (by linarith [N.epsilon_lt_half]) (sq_nonneg _)).trans h
    change (1 / 2 : ℝ) * ‖w‖ ^ 2 ≤ N.scale⁻¹ ^ 2 *
      g.parametrizedCoefficients (N.centeredParametrization q) (0, s) w w at hhalf
    have hh := mul_le_mul_of_nonneg_left hhalf (sq_nonneg N.scale)
    calc
      _ = N.scale ^ 2 * ((1 / 2 : ℝ) * ‖w‖ ^ 2) := by ring
      _ ≤ N.scale ^ 2 * (N.scale⁻¹ ^ 2 *
          g.parametrizedCoefficients (N.centeredParametrization q) (0, s) w w) := hh
      _ = _ := by field_simp [N.scale_pos.ne']
  have hell (w : EuclideanSpace ℝ (Fin 3)) :
      (a * N.scale ^ 2) * ‖w‖ ^ 2 ≤ g.pullbackCoefficients B p w w := by
    have h := quadratic_lower_rechart e
      (g.parametrizedCoefficients (N.centeredParametrization q) (0, s)) hlower w
    rw [hchart]
    change _ ≤ g.parametrizedCoefficients (N.centeredParametrization q ∘ e.symm) p w w
    erw [g.parametrizedCoefficients_comp_linear e.symm.toContinuousLinearMap
      ((N.centeredParametrization_contMDiffAt q (y := e.symm p)
        (by simpa only [p, e.symm_apply_apply] using hs)).mdifferentiableAt (by simp))]
    rw [show e.symm.toContinuousLinearMap p = (0, s) from e.symm_apply_apply _]
    exact h
  have hjet : ‖fderiv ℝ (g.pullbackCoefficients B) p‖ ≤ d * N.scale ^ 2 * N.epsilon := by
    rw [hchart]
    have h := N.norm_fderiv_centeredParametrization_rechart_le q hs e
    calc
      _ ≤ 216 * N.epsilon * N.scale ^ 2 * ‖e.symm.toContinuousLinearMap‖ ^ 3 := h
      _ = _ := by dsimp only [d]; ring
  have hunit : g.pullbackCoefficients B p v v = 1 := by
    have hpos : 0 ≤ g.inner x u u := by
      by_cases hz : u = 0
      · simp [hz]
      · exact (g.pos x u hz).le
    have hsq := congrArg (fun t : ℝ => t ^ 2) hu
    dsimp only [RiemannianMetric.tangentNorm] at hsq
    rw [Real.sq_sqrt hpos, one_pow] at hsq
    change g.inner (B p) (mfderiv (𝓡 3) (𝓡 3) B p v)
      (mfderiv (𝓡 3) (𝓡 3) B p v) = 1
    rw [hv, hpx]
    exact hsq
  have h := CoordinateExponential.abs_linear_christoffel_le_of_scaled_controls
    axialLinearCoordinate ha hd N.scale_pos N.epsilon_pos.le hell hjet hunit
  have hess := N.axial_hessian_of_euclidean_neckChart N.connection q hp v v
  change N.connection.hessian N.axialCoordinate (B p)
    (mfderiv (𝓡 3) (𝓡 3) B p v) (mfderiv (𝓡 3) (𝓡 3) B p v) = _ at hess
  rw [hv, hpx] at hess
  rw [hess, abs_neg]
  exact h

end PoincareConjecture.EpsilonNeck
