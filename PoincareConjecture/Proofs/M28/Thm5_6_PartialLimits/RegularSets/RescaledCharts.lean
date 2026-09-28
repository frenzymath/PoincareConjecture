import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.NormalCover
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.Rescaling











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace PoincareConjecture.M28.RegularNormalChartCover

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {p : M} {δ R ρ : ℝ} {N : ℕ}



noncomputable def unitBallMap (C : RegularNormalChartCover g p δ R ρ N)
    (i : Fin (N + 1)) (x : ball (0 : EuclideanSpace ℝ (Fin n)) 1) : M :=
  C.chart i ((ρ / 2) • (x : EuclideanSpace ℝ (Fin n)))



theorem unitBallMap_distances (C : RegularNormalChartCover g p δ R ρ N)
    (hρ : 0 < ρ) (i : Fin (N + 1))
    (x y : ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (Real.sqrt (1 / 4 : ℝ) * (ρ / 2)) * dist x y ≤
        (g.edist (C.unitBallMap i x) (C.unitBallMap i y)).toReal ∧
      (g.edist (C.unitBallMap i x) (C.unitBallMap i y)).toReal ≤
        (Real.sqrt (9 / 4 : ℝ) * (ρ / 2)) * dist x y := by
  have h := C.distances i _ (NormalChartCover.rescale_mem_half_ball hρ x)
    _ (NormalChartCover.rescale_mem_half_ball hρ y)
  simpa only [unitBallMap, dist_smul₀, Real.norm_eq_abs, abs_of_pos (half_pos hρ),
    mul_assoc, Subtype.dist_eq] using h



theorem unitBallMap_isLocalDiffeomorph
    (C : RegularNormalChartCover g p δ R ρ N)
    (hρ : 0 < ρ) (hρR : ρ / 2 ≤ R) (i : Fin (N + 1)) :
    letI : Nonempty (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := ⟨⟨0, by simp⟩⟩
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n))
        (ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
      isOpen_ball.isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (C.unitBallMap i) := by
  let : Nonempty (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := ⟨⟨0, by simp⟩⟩
  let : ChartedSpace (EuclideanSpace ℝ (Fin n))
      (ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isOpen_ball.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let L := (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin n))
    (ρ / 2) (ne_of_gt (half_pos hρ))).toContinuousLinearEquiv.toDiffeomorph
  intro x
  have hsub := Poincare.isLocalDiffeomorph_subtypeVal (𝓡 n)
    (ball (0 : EuclideanSpace ℝ (Fin n)) 1) isOpen_ball ∞ x
  have hL := hsub.comp (𝓡 n) _ (L.isLocalDiffeomorph (x : EuclideanSpace ℝ (Fin n)))
  have hx : (ρ / 2) • (x : EuclideanSpace ℝ (Fin n)) ∈ (C.chart i).source := by
    rw [C.source]
    exact (ball_subset_ball hρR) (NormalChartCover.rescale_mem_half_ball hρ x)
  exact hL.comp (𝓡 n) M ((C.chart i).isLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ hx)



theorem unitBallMap_isOpenEmbedding
    (C : RegularNormalChartCover g p δ R ρ N)
    (hρ : 0 < ρ) (hρR : ρ / 2 ≤ R) (i : Fin (N + 1)) :
    Topology.IsOpenEmbedding (C.unitBallMap i) := by
  let : Nonempty (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := ⟨⟨0, by simp⟩⟩
  let : ChartedSpace (EuclideanSpace ℝ (Fin n))
      (ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isOpen_ball.isOpenEmbedding_subtypeVal.singletonChartedSpace
  have hd := C.unitBallMap_isLocalDiffeomorph hρ hρR i
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    hd.contMDiff.continuous _ hd.isOpenMap
  intro x y hxy
  have hx : (ρ / 2) • (x : EuclideanSpace ℝ (Fin n)) ∈ (C.chart i).source := by
    rw [C.source]
    exact (ball_subset_ball hρR) (NormalChartCover.rescale_mem_half_ball hρ x)
  have hy : (ρ / 2) • (y : EuclideanSpace ℝ (Fin n)) ∈ (C.chart i).source := by
    rw [C.source]
    exact (ball_subset_ball hρR) (NormalChartCover.rescale_mem_half_ball hρ y)
  apply Subtype.ext
  exact (smul_right_injective _ (ne_of_gt (half_pos hρ)))
    ((C.chart i).injOn hx hy hxy)



theorem unitBallMap_cover (C : RegularNormalChartCover g p δ R ρ N)
    (hρ : 0 < ρ) :
    regularComponent g p (4 * δ) ⊆ ⋃ i, C.unitBallMap i ''
      {x : ball (0 : EuclideanSpace ℝ (Fin n)) 1 |
        ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ 1 / 4} := by
  intro q hq
  obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp (C.cover hq)
  have hy' : ‖y‖ ≤ ρ / 8 := mem_closedBall_zero_iff.mp hy
  let x := (ρ / 2)⁻¹ • y
  have hx : ‖x‖ ≤ 1 / 4 := by
    dsimp [x]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (half_pos hρ))]
    apply (inv_mul_le_iff₀ (half_pos hρ)).mpr
    nlinarith
  refine mem_iUnion.mpr ⟨i, ⟨⟨x, mem_ball_zero_iff.mpr (hx.trans_lt (by norm_num))⟩,
    hx, ?_⟩⟩
  dsimp [unitBallMap, x]
  rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (half_pos hρ)), one_smul]




theorem unitBallMap_mem_regularComponent
    (C : RegularNormalChartCover g p δ R ρ N)
    (hρ : 0 < ρ) (hρR : ρ / 2 ≤ R) (i : Fin (N + 1))
    (x : ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    C.unitBallMap i x ∈ regularComponent g p (2 * δ) := by
  apply C.target_regular i
  apply (C.chart i).map_source
  rw [C.source]
  exact (ball_subset_ball hρR) (NormalChartCover.rescale_mem_half_ball hρ x)

end PoincareConjecture.M28.RegularNormalChartCover
