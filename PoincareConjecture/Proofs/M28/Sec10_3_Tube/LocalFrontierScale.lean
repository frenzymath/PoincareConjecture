import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderUniformScalar
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckQuarterOverlap
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_ambient_scalar_control_on_closure_m28 {α : ℝ} (hα : 0 < α) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N : EpsilonNeck g) (D : LeviCivitaData g), N.epsilon ≤ ε₀ →
      ∀ x ∈ closure N.carrier,
        |N.scale ^ 2 * D.scalarCurvature x - 1| ≤ α := by
  obtain ⟨ε₀, hpos, hsmall, hcontrol⟩ :=
    PoincareConjecture.M28.tube.exists_cylinder_scalar_accuracy hα
  refine ⟨ε₀, hpos, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N D hε x hx
  have hinterior (y : M) (hy : y ∈ N.carrier) :
      |N.scale ^ 2 * D.scalarCurvature y - 1| ≤ α := by
    exact (hcontrol M g D N hε y hy).le
  exact le_on_closure hinterior
    (((continuous_const.mul D.continuous_scalarCurvature).sub continuous_const).abs.continuousOn)
    continuous_const.continuousOn hx

theorem exists_scale_comparison_at_common_closure_m28 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N N' : EpsilonNeck g), N.epsilon ≤ ε₀ → N'.epsilon ≤ ε₀ →
      (closure N.carrier ∩ closure N'.carrier).Nonempty →
        (0.99 : ℝ) * N.scale ≤ N'.scale ∧
          N'.scale ≤ (1.01 : ℝ) * N.scale := by
  obtain ⟨ε₀, hpos, hsmall, hcontrol⟩ :=
    exists_ambient_scalar_control_on_closure_m28.{u}
      (α := 1 / 1000) (by norm_num)
  refine ⟨ε₀, hpos, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N N' hN hN' ⟨x, hx, hx'⟩
  have hs := abs_le.mp (hcontrol N N.connection hN x hx)
  have ht := abs_le.mp (hcontrol N' N.connection hN' x hx')
  have hQ : 0 < N.connection.scalarCurvature x := by
    by_contra h
    have hmul := mul_nonpos_of_nonneg_of_nonpos
      (sq_nonneg N.scale) (le_of_not_gt h)
    linarith
  have hscale : (0.99 : ℝ) * N.scale ≤ N'.scale := by
    have hsq : (0.99 : ℝ) ^ 2 * N.scale ^ 2 ≤ N'.scale ^ 2 := by
      apply (mul_le_mul_iff_left₀ hQ).mp
      nlinarith [hs.2, ht.1]
    nlinarith [N.scale_pos, N'.scale_pos]
  have hscale' : N'.scale ≤ (1.01 : ℝ) * N.scale := by
    have hsq : N'.scale ^ 2 ≤ (1.01 : ℝ) ^ 2 * N.scale ^ 2 := by
      apply (mul_le_mul_iff_left₀ hQ).mp
      nlinarith [hs.1, ht.2]
    nlinarith [N.scale_pos, N'.scale_pos]
  exact ⟨hscale, hscale'⟩

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem edist_le_of_mem_positive_quarter_m28 (N : EpsilonNeck g)
    (hε : N.epsilon ≤ 1 / 1000) {x y : M}
    (hx : x ∈ N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹)
    (hy : y ∈ N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) :
    g.edist x y ≤ ENNReal.ofReal ((0.51 : ℝ) * N.scale * N.epsilon⁻¹) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let z := N.coordinate_inverse x
  let w := N.coordinate_inverse y
  have hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (N.coordinate_inverse_mem x hx.1).2
  have hw : w.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (N.coordinate_inverse_mem y hy.1).2
  have hxy : g.edist x y ≤ ENNReal.ofReal
      (N.scale * Real.sqrt (1 + N.epsilon) * Real.sqrt 2 * Real.pi) +
      ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon) * |w.2 - z.2|) := by
    calc
      _ = g.edist (N.coordinate_map (z.1, z.2))
          (N.coordinate_map (w.1, w.2)) := by
        rw [Prod.eta, Prod.eta, N.coordinate_map_coordinate_inverse hx.1,
          N.coordinate_map_coordinate_inverse hy.1]
      _ ≤ g.edist (N.coordinate_map (z.1, z.2)) (N.coordinate_map (w.1, z.2)) +
          g.edist (N.coordinate_map (w.1, z.2)) (N.coordinate_map (w.1, w.2)) :=
        Manifold.riemannianEDist_triangle
      _ ≤ _ := add_le_add (N.edist_coordinate_map_slice_le z.1 w.1 hz)
        (N.edist_coordinate_map_axis_le w.1 hz hw)
  have haxis : |w.2 - z.2| ≤ N.epsilon⁻¹ / 2 := by
    apply abs_le.mpr
    dsimp [z, w]
    constructor <;> linarith [hx.2.1, hx.2.2, hy.2.1, hy.2.2]
  have hinv : (1000 : ℝ) ≤ N.epsilon⁻¹ := by
    have h := mul_le_mul_of_nonneg_right hε (inv_pos.mpr N.epsilon_pos).le
    rw [mul_inv_cancel₀ N.epsilon_pos.ne'] at h
    linarith
  have hroot : Real.sqrt (1 + N.epsilon) ≤ (1.001 : ℝ) := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 + N.epsilon by linarith [N.epsilon_pos])
    nlinarith [Real.sqrt_nonneg (1 + N.epsilon)]
  have hsphere : Real.sqrt (1 + N.epsilon) * Real.sqrt 2 ≤ 2 := by
    have hsq : (Real.sqrt (1 + N.epsilon) * Real.sqrt 2) ^ 2 =
        (1 + N.epsilon) * 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith [N.epsilon_pos]),
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith [N.epsilon_lt_half, mul_nonneg (Real.sqrt_nonneg (1 + N.epsilon))
      (Real.sqrt_nonneg 2)]
  have hnum : Real.sqrt (1 + N.epsilon) * Real.sqrt 2 * Real.pi +
      Real.sqrt (1 + N.epsilon) * |w.2 - z.2| ≤ (0.51 : ℝ) * N.epsilon⁻¹ := by
    have h1 := mul_le_mul_of_nonneg_right hsphere Real.pi_pos.le
    have h2 := mul_le_mul hroot haxis (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1.001)
    nlinarith [Real.pi_le_four]
  apply hxy.trans
  have hscale_pos := N.scale_pos
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [mul_le_mul_of_nonneg_left hnum N.scale_pos.le]

theorem edist_le_of_mem_closure_positive_quarter_m28 (N : EpsilonNeck g)
    (hε : N.epsilon ≤ 1 / 1000) {x y : M}
    (hx : x ∈ N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹)
    (hy : y ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹)) :
    g.edist x y ≤ ENNReal.ofReal ((0.51 : ℝ) * N.scale * N.epsilon⁻¹) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  exact closure_minimal (fun z hz => N.edist_le_of_mem_positive_quarter_m28 hε hx hz)
    (isClosed_le (continuous_const.edist continuous_id) continuous_const) hy

end PoincareConjecture.EpsilonNeck
