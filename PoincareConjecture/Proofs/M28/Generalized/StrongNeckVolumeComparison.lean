import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderScalarReadout
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckLengthComparison
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.SphereMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology BigOperators

universe u

namespace PoincareConjecture.M28

open tube PoincareConjecture.Proofs.M28.NeckAnalysis

private abbrev E := EuclideanSpace ℝ (Fin 3)

private theorem cylinder_coordinates_norm_sq (v : E) :
    ‖v‖ ^ 2 = ‖(cylinderScalarCoordinateEquiv v).1‖ ^ 2 +
      (cylinderScalarCoordinateEquiv v).2 ^ 2 := by
  simp [cylinderScalarCoordinateEquiv_apply, EuclideanSpace.real_norm_sq_eq,
    Fin.sum_univ_succ]
  ring

private theorem sphere_conformal_bounds {x : EuclideanSpace ℝ (Fin 2)}
    (hx : ‖x‖ ≤ 1) : (1 / 2 : ℝ) ≤ sphereChartConformalFactor x ∧
      sphereChartConformalFactor x ≤ 1 := by
  have hx0 := norm_nonneg x
  have hx2 : ‖x‖ ^ 2 ≤ 1 := by nlinarith
  have hd : 0 < (‖x‖ ^ 2 + 4) ^ 2 := by positivity
  unfold sphereChartConformalFactor
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith [sq_nonneg (‖x‖ ^ 2), sq_nonneg (1 - ‖x‖ ^ 2)]
  · apply (div_le_iff₀ hd).mpr
    nlinarith [sq_nonneg (‖x‖ ^ 2)]

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

theorem normalized_neck_chart_speed_bounds (N : EpsilonNeck g)
    (hscale : N.scale = 1) (q : UnitTwoSphere) (s : ℝ) {x : E}
    (hx : x ∈ cylinderNeckChartDomain N q s) (hxnorm : ‖x‖ ≤ 1) (v : E) :
    (1 / 2 : ℝ) * ‖v‖ ≤
        g.tangentNorm (cylinderNeckChart N q s x)
          (mfderiv (𝓡 3) (𝓡 3) (cylinderNeckChart N q s) x v) ∧
      g.tangentNorm (cylinderNeckChart N q s x)
          (mfderiv (𝓡 3) (𝓡 3) (cylinderNeckChart N q s) x v) ≤ 4 * ‖v‖ := by
  let u := (cylinderScalarCoordinates s x).1
  let z := cylinderSphereParametrization q (cylinderScalarCoordinates s x)
  let w : RoundCylinderCoordinates :=
    (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm u
      (cylinderScalarCoordinateEquiv v).1, (cylinderScalarCoordinateEquiv v).2)
  have hu : u = (cylinderScalarCoordinateEquiv x).1 := by
    simp [u, cylinderScalarCoordinates]
  have hu1 : ‖u‖ ≤ 1 := by
    rw [hu]
    have hnorm := cylinder_coordinates_norm_sq x
    nlinarith [norm_nonneg (cylinderScalarCoordinateEquiv x).1, norm_nonneg x,
      sq_nonneg (cylinderScalarCoordinateEquiv x).2]
  have hform : RoundCylinderMetric z w w =
      2 * sphereChartConformalFactor u * ‖(cylinderScalarCoordinateEquiv v).1‖ ^ 2 +
        (cylinderScalarCoordinateEquiv v).2 ^ 2 := by
    dsimp only [RoundCylinderMetric, EvolvingRoundCylinderMetric, z, w,
      cylinderSphereParametrization]
    rw [sphere_chart_inverse_inner_at]
    rw [real_inner_self_eq_norm_sq]
    ring
  obtain ⟨hfactorlow, hfactorhigh⟩ := sphere_conformal_bounds hu1
  have hnorm := cylinder_coordinates_norm_sq v
  have hquadratic : ‖v‖ ^ 2 ≤ RoundCylinderMetric z w w ∧
      RoundCylinderMetric z w w ≤ 2 * ‖v‖ ^ 2 := by
    rw [hform]
    have hl := mul_le_mul_of_nonneg_right hfactorlow
      (sq_nonneg ‖(cylinderScalarCoordinateEquiv v).1‖)
    have hh := mul_le_mul_of_nonneg_right hfactorhigh
      (sq_nonneg ‖(cylinderScalarCoordinateEquiv v).1‖)
    constructor <;> nlinarith [sq_nonneg (cylinderScalarCoordinateEquiv v).2]
  have hnonneg : 0 ≤ RoundCylinderMetric z w w :=
    (sq_nonneg ‖v‖).trans hquadratic.1
  have hsqrtlow : ‖v‖ ≤ Real.sqrt (RoundCylinderMetric z w w) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hnonneg]
    exact hquadratic.1
  have hsqrthigh : Real.sqrt (RoundCylinderMetric z w w) ≤ 2 * ‖v‖ := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt hnonneg]
    nlinarith [sq_nonneg ‖v‖]
  have hspeed := N.coordinate_speed_bounds z hx.2 w
  rw [hscale] at hspeed
  rw [cylinderNeckChart_mfderiv_apply N q s hx]
  change (1 / 2 : ℝ) * ‖v‖ ≤ g.tangentNorm (N.coordinate_map z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z w) ∧
    g.tangentNorm (N.coordinate_map z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map z w) ≤ 4 * ‖v‖
  constructor <;> nlinarith [hspeed.1, hspeed.2]

end PoincareConjecture.M28
