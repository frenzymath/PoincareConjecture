import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.SourceCharts.Coefficients











set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {g : ℝ → RiemannianMetric n M} {p : M}
  {T' T A R ρ a b : ℝ} {N : ℕ}



theorem normalChart_unitBallMap_mem_ball
    (C : NormalChartCover g p T' T A R ρ a b N)
    (hρ : 0 < ρ) (hρR : ρ / 2 ≤ R) (i : Fin (N + 1))
    (x : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    C.unitBallMap i x ∈ (g 0).ball p (A + ρ / 2) := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(g 0).toRiemannianMetric⟩
  have hxhalf := NormalChartCover.rescale_mem_half_ball hρ x
  have hxR := Metric.ball_subset_ball hρR hxhalf
  have hcentre : (g 0).edist p (C.centre i) < ENNReal.ofReal A :=
    C.centre_mem i
  have hA : 0 < A :=
    ENNReal.ofReal_pos.mp (zero_le.trans_lt hcentre)
  have hnear : (g 0).edist (C.centre i) (C.unitBallMap i x) <
      ENNReal.ofReal (ρ / 2) := by
    rw [NormalChartCover.unitBallMap, C.radial_distance i _ hxR]
    exact (ENNReal.ofReal_lt_ofReal_iff (half_pos hρ)).mpr
      (mem_ball_zero_iff.mp hxhalf)
  change (g 0).edist p (C.unitBallMap i x) < ENNReal.ofReal (A + ρ / 2)
  rw [ENNReal.ofReal_add hA.le (half_pos hρ).le]
  have htriangle : (g 0).edist p (C.unitBallMap i x) ≤
      (g 0).edist p (C.centre i) +
        (g 0).edist (C.centre i) (C.unitBallMap i x) :=
    Manifold.riemannianEDist_triangle
  exact htriangle.trans_lt (ENNReal.add_lt_add hcentre hnear)

local instance :
    Nonempty (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  ⟨⟨0, by simp⟩⟩




theorem normalChart_unitBallMap_upper_coefficients
    (C : NormalChartCover g p T' T A R ρ a b N)
    (hρ : 0 < ρ) (hρR : ρ / 2 ≤ R) (i : Fin (N + 1))
    {t : ℝ} (ht : t ∈ Ioo T' T)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.ball 0 1)
    (v : EuclideanSpace ℝ (Fin n)) :
    (g t).pullbackCoefficients
        (ChartDistance.chartParametrization
          (fun _ : ℕ => Metric.ball 0 1)
          (fun _ => isOpen_ball) (i := 0) (C.unitBallMap i)) x v v ≤
      (b * (ρ / 2) ^ 2) * ‖v‖ ^ 2 := by
  rw [NormalChartCover.unitBallMap_pullbackCoefficients C hρ hρR i t hx]
  have hx' : (ρ / 2) • x ∈ Metric.closedBall 0 (2 * ρ) :=
    (Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by linarith)))
      (NormalChartCover.rescale_mem_half_ball hρ ⟨x, hx⟩)
  have h := mul_le_mul_of_nonneg_left
    (C.coefficients i t ht _ hx' v).2 (sq_nonneg (ρ / 2))
  nlinarith only [h]

end PoincareConjecture.M30
