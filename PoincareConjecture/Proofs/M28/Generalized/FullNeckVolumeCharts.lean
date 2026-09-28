import PoincareConjecture.Proofs.M28.Generalized.StrongNeckVolumeImages

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal BigOperators

universe u

namespace PoincareConjecture.M28

open tube PoincareConjecture.Proofs.M28.NeckAnalysis

private abbrev E := EuclideanSpace ℝ (Fin 3)

private theorem full_neck_coordinates_norm_sq (v : E) :
    ‖v‖ ^ 2 = ‖(cylinderScalarCoordinateEquiv v).1‖ ^ 2 +
      (cylinderScalarCoordinateEquiv v).2 ^ 2 := by
  simp [cylinderScalarCoordinateEquiv_apply, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_succ]
  ring

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem full_neck_chart_speed_upper (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) {x : E}
    (hx : x ∈ cylinderNeckChartDomain N q s) (v : E) :
    g.tangentNorm (cylinderNeckChart N q s x)
      (mfderiv (𝓡 3) (𝓡 3) (cylinderNeckChart N q s) x v) ≤
        (4 * N.scale) * ‖v‖ := by
  let u := (cylinderScalarCoordinates s x).1
  let z := cylinderSphereParametrization q (cylinderScalarCoordinates s x)
  let w : RoundCylinderCoordinates :=
    (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm u
      (cylinderScalarCoordinateEquiv v).1, (cylinderScalarCoordinateEquiv v).2)
  have hfactor : sphereChartConformalFactor u ≤ 1 := by
    unfold sphereChartConformalFactor
    apply (div_le_iff₀ (by positivity : 0 < (‖u‖ ^ 2 + 4) ^ 2)).mpr
    nlinarith only [sq_nonneg ‖u‖, sq_nonneg (‖u‖ ^ 2)]
  have hform : RoundCylinderMetric z w w =
      2 * sphereChartConformalFactor u * ‖(cylinderScalarCoordinateEquiv v).1‖ ^ 2 +
        (cylinderScalarCoordinateEquiv v).2 ^ 2 := by
    dsimp only [RoundCylinderMetric, EvolvingRoundCylinderMetric, z, w,
      cylinderSphereParametrization]
    rw [sphere_chart_inverse_inner_at, real_inner_self_eq_norm_sq]
    ring
  have hnonneg : 0 ≤ RoundCylinderMetric z w w := by
    rw [hform]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (sphereChartConformalFactor_pos u).le)
        (sq_nonneg _)) (sq_nonneg _)
  have hquadratic : RoundCylinderMetric z w w ≤ 2 * ‖v‖ ^ 2 := by
    rw [hform]
    have hh := mul_le_mul_of_nonneg_right hfactor
      (sq_nonneg ‖(cylinderScalarCoordinateEquiv v).1‖)
    have hn := full_neck_coordinates_norm_sq v
    nlinarith only [hh, hn, sq_nonneg (cylinderScalarCoordinateEquiv v).2]
  have hsqrt : Real.sqrt (RoundCylinderMetric z w w) ≤ 2 * ‖v‖ := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt hnonneg]
    nlinarith only [hquadratic, sq_nonneg ‖v‖]
  have hspeed := (N.coordinate_speed_bounds z hx.2 w).2
  rw [cylinderNeckChart_mfderiv_apply N q s hx]
  change g.tangentNorm (N.coordinate_map z)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z w) ≤
      (4 * N.scale) * ‖v‖
  calc
    _ ≤ (2 * N.scale) * Real.sqrt (RoundCylinderMetric z w w) := hspeed
    _ ≤ (2 * N.scale) * (2 * ‖v‖) :=
      mul_le_mul_of_nonneg_left hsqrt
        (mul_nonneg (by norm_num) N.scale_pos.le)
    _ = (4 * N.scale) * ‖v‖ := by ring

theorem full_neck_chart_density_upper (N : EpsilonNeck g)
    (q : UnitTwoSphere) (s : ℝ) {x : E}
    (hx : x ∈ cylinderNeckChartDomain N q s) :
    g.pullbackVolumeDensity (cylinderNeckChart N q s) x ≤ 384 * N.scale ^ 3 := by
  have hi := (cylinderNeckChart_mfderiv_isInvertible N q s hx).bijective.1
  have h := g.pullbackVolumeDensity_le_of_differential_bound hi
    (full_neck_chart_speed_upper N q s hx)
  calc
    _ ≤ (Nat.factorial 3 : ℝ) * (4 * N.scale) ^ 3 := h
    _ = 384 * N.scale ^ 3 := by norm_num [mul_pow]; ring

theorem full_neck_chart_image_volume_upper
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    (N : EpsilonNeck g) (q : UnitTwoSphere) (s : ℝ)
    {U : Set E} (hU : MeasurableSet U)
    (hUdomain : U ⊆ cylinderNeckChartDomain N q s) :
    g.volumeMeasure (cylinderNeckChart N q s '' U) ≤
      ENNReal.ofReal (384 * N.scale ^ 3) * volume U := by
  have hUe : U ⊆ (neckVolumeChart N q s).source := by
    rw [neckVolumeChart_source]
    exact hUdomain
  have heq := g.volumeMeasure_image_eq_lintegral_pullbackVolumeDensity
    (neckVolumeChart N q s) (neckVolumeChart_smooth N q s)
    (neckVolumeChart_symm_smooth N q s) hU hUe
  change g.volumeMeasure (cylinderNeckChart N q s '' U) =
    ∫⁻ x in U, ENNReal.ofReal (g.pullbackVolumeDensity (cylinderNeckChart N q s) x) at heq
  rw [heq, ← setLIntegral_const]
  exact setLIntegral_mono' hU (fun x hx => ENNReal.ofReal_le_ofReal
    (full_neck_chart_density_upper N q s (hUdomain hx)))

end PoincareConjecture.M28
