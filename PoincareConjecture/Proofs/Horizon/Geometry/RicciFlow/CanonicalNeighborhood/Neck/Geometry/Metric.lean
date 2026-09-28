import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Jet
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Frame
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Evaluation









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff Bundle BigOperators
universe u
namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

theorem normalized_pullback_quadratic_error
    {z : RoundCylinderSpace} (hz : z.2 ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v : RoundCylinderTangent z) :
    |N.normalized_pullback z v v - EvolvingRoundCylinderMetric 0 z v v| ≤
      N.epsilon * EvolvingRoundCylinderMetric 0 z v v := by
  let : Bundle.RiemannianBundle (RoundCylinderTangent : RoundCylinderSpace → Type _) :=
    ⟨roundCylinderProductMetric.toRiemannianMetric⟩
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
  let p : RoundCylinderCoordinates := (c z.1, z.2)
  let x : RoundCylinderSpace := (c.symm p.1, p.2)
  let b := roundCylinderChartBasis z.1 p
  let : FiniteDimensional ℝ (RoundCylinderTangent x) := Module.Finite.of_basis b
  let D := mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate_map x
  let A : RoundCylinderTangent x →ₗ[ℝ] RoundCylinderTangent x →ₗ[ℝ] ℝ :=
    (N.scale⁻¹ ^ 2) • (g.inner (N.coordinate_map x)).toBilinForm.comp
      D.toLinearMap D.toLinearMap - (roundCylinderProductMetric.inner x).toBilinForm
  have hGram : Matrix.of (fun i j => inner ℝ (b i) (b j)) = roundCylinderGram 0 c p := by
    ext i j
    simp only [Matrix.of_apply, b, roundCylinderChartBasis_apply]
    exact roundCylinderChartFrame_gram z.1 p i j
  have hcoef (i j : Fin 3) : A (b i) (b j) =
      roundCylinderTensorCoefficient N.normalized_pullback c p i j -
        roundCylinderGram 0 c p i j := by
    change N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map x
      (b i) (b j) - roundCylinderProductMetric.inner x (b i) (b j) = _
    rw [roundCylinderProductMetric_inner]
    simp only [b, roundCylinderChartBasis_apply]
    rfl
  have hA : (∑ i : Fin 2 → Fin 3, ∑ j : Fin 2 → Fin 3,
      (∏ r, (Matrix.of (fun i j => inner ℝ (b i) (b j)))⁻¹ (i r) (j r)) *
        A (b (i 0)) (b (i 1)) * A (b (j 0)) (b (j 1))) ≤ N.epsilon ^ 2 := by
    simp only [hGram, hcoef]
    exact (N.normalized_pullback_zeroth_normSquared_lt hz).le
  have hx : x = z := by
    apply Prod.ext
    · exact c.left_inv (mem_chart_source _ z.1)
    · rfl
  have hbound : ∀ w : RoundCylinderTangent x,
      |N.normalized_pullback x w w - EvolvingRoundCylinderMetric 0 x w w| ≤
        N.epsilon * EvolvingRoundCylinderMetric 0 x w w := by
    intro w
    have h := abs_bilinear_apply_self_le_of_inverse_gram_contraction_le A b
      N.epsilon_pos.le hA w
    change |N.normalized_pullback x w w - roundCylinderProductMetric.inner x w w| ≤
      N.epsilon * roundCylinderProductMetric.inner x w w at h
    simpa only [roundCylinderProductMetric_inner] using h
  have hbound' : ∀ w : RoundCylinderTangent z,
      |N.normalized_pullback z w w - EvolvingRoundCylinderMetric 0 z w w| ≤
        N.epsilon * EvolvingRoundCylinderMetric 0 z w w := by
    exact Eq.mp (congrArg (fun y : RoundCylinderSpace =>
      ∀ w : RoundCylinderTangent y,
        |N.normalized_pullback y w w - EvolvingRoundCylinderMetric 0 y w w| ≤
          N.epsilon * EvolvingRoundCylinderMetric 0 y w w) hx) hbound
  exact hbound' v

theorem pullback_metric_bounds
    {z : RoundCylinderSpace} (hz : z.2 ∈ Set.Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (v : RoundCylinderTangent z) :
    (1 - N.epsilon) * N.scale ^ 2 * EvolvingRoundCylinderMetric 0 z v v ≤
        roundCylinderPullback g N.coordinate_map z v v ∧
      roundCylinderPullback g N.coordinate_map z v v ≤
        (1 + N.epsilon) * N.scale ^ 2 * EvolvingRoundCylinderMetric 0 z v v := by
  have h := abs_le.mp (N.normalized_pullback_quadratic_error hz v)
  dsimp only [normalized_pullback] at h
  have hs : 0 < N.scale ^ 2 := sq_pos_of_pos N.scale_pos
  have hcancel : N.scale ^ 2 * (N.scale⁻¹ ^ 2 *
      roundCylinderPullback g N.coordinate_map z v v) =
      roundCylinderPullback g N.coordinate_map z v v := by
    field_simp [N.scale_pos.ne']
  have hlo := mul_le_mul_of_nonneg_left h.1 hs.le
  have hhi := mul_le_mul_of_nonneg_left h.2 hs.le
  constructor <;> nlinarith [hcancel]

end PoincareConjecture.EpsilonNeck
