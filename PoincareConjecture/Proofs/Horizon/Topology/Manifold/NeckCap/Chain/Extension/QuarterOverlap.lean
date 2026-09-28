import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.FrontierScale
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain.Extension.DistanceLower
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Diameter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] {g : RiemannianMetric 3 M}

theorem edist_le_of_mem_positive_quarter (N : EpsilonNeck g)
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

theorem edist_le_of_mem_closure_positive_quarter (N : EpsilonNeck g)
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
  exact closure_minimal (fun z hz => N.edist_le_of_mem_positive_quarter hε hx hz)
    (isClosed_le (continuous_const.edist continuous_id) continuous_const) hy

theorem exists_positive_quarter_subset_frontier_neck_threshold :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 1000 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N N' : EpsilonNeck g), N.epsilon ≤ ε₀ → N'.epsilon = N.epsilon →
      N'.center ∈ closure (N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹) →
      N.region (N.epsilon⁻¹ / 2) N.epsilon⁻¹ ⊆ N'.carrier := by
  obtain ⟨ε₁, hε₁, _, hscale⟩ := exists_scale_comparison_on_closure.{u}
  refine ⟨min ε₁ (1 / 1000), lt_min hε₁ (by norm_num), min_le_right _ _, ?_⟩
  intro M _ _ _ _ _ _ _ g N N' hε heq hcenter x hx
  have hsmall : N.epsilon ≤ 1 / 1000 := hε.trans (min_le_right _ _)
  have hs := (hscale N N' (hε.trans (min_le_left _ _))
    (closure_mono (N.region_subset_carrier _ _) hcenter)).1
  by_contra hout
  have hlower := N'.balanced_edist_lower_of_not_mem_carrier (heq ▸ hsmall) hout
  rw [heq] at hlower
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hupper := N.edist_le_of_mem_closure_positive_quarter hsmall hx hcenter
  have hcomm : g.edist x N'.center = g.edist N'.center x := Manifold.riemannianEDist_comm
  rw [hcomm] at hupper
  have hlt : ENNReal.ofReal ((0.51 : ℝ) * N.scale * N.epsilon⁻¹) <
      ENNReal.ofReal ((0.99 : ℝ) * N'.scale * N.epsilon⁻¹) := by
    have hscale_pos := N.scale_pos
    have hscale'_pos := N'.scale_pos
    have hinv_pos := inv_pos.mpr N.epsilon_pos
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    have h := mul_le_mul_of_nonneg_right hs hinv_pos.le
    nlinarith [mul_pos hscale_pos hinv_pos]
  exact (not_lt_of_ge (hlower.trans hupper)) hlt

end PoincareConjecture.EpsilonNeck
