import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.DistanceBounds
import PoincareConjecture.Proofs.M07.Geometry.Manifold.LocalDiffeomorph











noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.NormalChartCover

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : ℝ → RiemannianMetric n M} {p : M}
  {T' T A R ρ a b : ℝ} {N : ℕ}

def unitBallMap (C : NormalChartCover g p T' T A R ρ a b N) (i : Fin (N + 1))
    (x : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) : M :=
  C.chart i ((ρ / 2) • (x : EuclideanSpace ℝ (Fin n)))

theorem rescale_mem_half_ball (hρ : 0 < ρ)
    (x : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (ρ / 2) • (x : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball 0 (ρ / 2) := by
  rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hρ)]
  simpa using mul_lt_mul_of_pos_left (mem_ball_zero_iff.mp x.property) (half_pos hρ)

theorem unitBallMap_distances (C : NormalChartCover g p T' T A R ρ a b N)
    (hρ : 0 < ρ) (i : Fin (N + 1))
    (x y : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (Real.sqrt a * (ρ / 2)) * dist x y ≤
        ((g 0).edist (C.unitBallMap i x) (C.unitBallMap i y)).toReal ∧
      ((g 0).edist (C.unitBallMap i x) (C.unitBallMap i y)).toReal ≤
        (Real.sqrt b * (ρ / 2)) * dist x y := by
  have h := C.distances i _ (rescale_mem_half_ball hρ x) _ (rescale_mem_half_ball hρ y)
  simpa only [unitBallMap, dist_smul₀, Real.norm_eq_abs, abs_of_pos (half_pos hρ),
    mul_assoc, Subtype.dist_eq] using h

theorem unitBallMap_isLocalDiffeomorph
    (C : NormalChartCover g p T' T A R ρ a b N)
    (hρ : 0 < ρ) (hρR : ρ / 2 ≤ R) (i : Fin (N + 1)) :
    letI : Nonempty (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
      ⟨⟨0, by simp⟩⟩
    letI := (isOpen_ball (x := (0 : EuclideanSpace ℝ (Fin n))) (ε := 1)).isOpenEmbedding_subtypeVal.singletonChartedSpace
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (C.unitBallMap i) := by
  let : Nonempty (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := ⟨⟨0, by simp⟩⟩
  let := (isOpen_ball (x := (0 : EuclideanSpace ℝ (Fin n))) (ε := 1)).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let L := (LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin n))
    (ρ / 2) (ne_of_gt (half_pos hρ))).toContinuousLinearEquiv.toDiffeomorph
  intro x
  have hsub := Poincare.isLocalDiffeomorph_subtypeVal (𝓡 n)
    (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) isOpen_ball ∞ x
  have hL := hsub.comp (𝓡 n) _ (L.isLocalDiffeomorph (x : EuclideanSpace ℝ (Fin n)))
  have hx : (ρ / 2) • (x : EuclideanSpace ℝ (Fin n)) ∈ (C.chart i).source := by
    rw [C.source]
    exact (Metric.ball_subset_ball hρR) (rescale_mem_half_ball hρ x)
  exact hL.comp (𝓡 n) M ((C.chart i).isLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ hx)

theorem unitBallMap_isOpenEmbedding
    (C : NormalChartCover g p T' T A R ρ a b N)
    (hρ : 0 < ρ) (hρR : ρ / 2 ≤ R) (i : Fin (N + 1)) :
    Topology.IsOpenEmbedding (C.unitBallMap i) := by
  let : Nonempty (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := ⟨⟨0, by simp⟩⟩
  let := (isOpen_ball (x := (0 : EuclideanSpace ℝ (Fin n))) (ε := 1)).isOpenEmbedding_subtypeVal.singletonChartedSpace
  have hd := C.unitBallMap_isLocalDiffeomorph hρ hρR i
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    hd.contMDiff.continuous _ hd.isOpenMap
  intro x y hxy
  have hx : (ρ / 2) • (x : EuclideanSpace ℝ (Fin n)) ∈ (C.chart i).source := by
    rw [C.source]
    exact (Metric.ball_subset_ball hρR) (rescale_mem_half_ball hρ x)
  have hy : (ρ / 2) • (y : EuclideanSpace ℝ (Fin n)) ∈ (C.chart i).source := by
    rw [C.source]
    exact (Metric.ball_subset_ball hρR) (rescale_mem_half_ball hρ y)
  apply Subtype.ext
  exact (smul_right_injective _ (ne_of_gt (half_pos hρ)))
    ((C.chart i).injOn hx hy hxy)

theorem unitBallMap_cover (C : NormalChartCover g p T' T A R ρ a b N)
    (hρ : 0 < ρ) :
    (g 0).ball p A ⊆ ⋃ i, C.unitBallMap i ''
      {x : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 |
        ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ 1 / 2} := by
  intro q hq
  obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp (C.cover hq)
  have hy' : ‖y‖ ≤ ρ / 4 := mem_closedBall_zero_iff.mp hy
  let x := (ρ / 2)⁻¹ • y
  have hx : ‖x‖ ≤ 1 / 2 := by
    dsimp [x]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (half_pos hρ))]
    apply (inv_mul_le_iff₀ (half_pos hρ)).mpr
    nlinarith
  refine mem_iUnion.mpr ⟨i, ⟨⟨x, mem_ball_zero_iff.mpr (hx.trans_lt (by norm_num))⟩,
    hx, ?_⟩⟩
  dsimp [unitBallMap, x]
  rw [smul_smul]
  have hscalar : (ρ / 2) * (ρ / 2)⁻¹ = (1 : ℝ) :=
    mul_inv_cancel₀ (ne_of_gt (half_pos hρ))
  rw [hscalar, one_smul]

end PoincareConjecture.NormalChartCover
