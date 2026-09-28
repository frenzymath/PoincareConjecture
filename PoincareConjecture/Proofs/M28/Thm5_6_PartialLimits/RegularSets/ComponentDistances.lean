import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.NormalCover
import Mathlib.Topology.Order.IntermediateValue











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.M28.RegularNormalChartCover

variable {n : ℕ} {M : Type u} [MetricSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {p : M} {δ R ρ : ℝ} {N : ℕ}




theorem base_distance_le (C : RegularNormalChartCover g p δ R ρ N)
    (hdist : ∀ x y : M, edist x y = g.edist x y)
    (hρ : 0 < ρ) (hρR : 2 * ρ < R)
    {x : M} (hx : x ∈ regularComponent g p (4 * δ)) :
    dist p x ≤ (ρ / 2) * (N + 1 : ℕ) := by
  classical
  have hp : p ∈ regularComponent g p (4 * δ) := by
    simpa only [C.centre_zero] using C.centre_mem 0
  have hcover : ∀ y ∈ regularComponent g p (4 * δ),
      ∃ i : Fin (N + 1), dist y (C.centre i) ≤ ρ / 8 := by
    intro y hy
    obtain ⟨i, w, hw, rfl⟩ := mem_iUnion.mp (C.cover hy)
    refine ⟨i, ?_⟩
    have hwR : w ∈ ball 0 R :=
      closedBall_subset_ball (by linarith : ρ / 8 < R) hw
    rw [dist_comm, dist_edist, hdist, C.radial_distance i w hwR,
      ENNReal.toReal_ofReal (norm_nonneg _)]
    exact mem_closedBall_zero_iff.mp hw
  by_contra hbound
  have hfar : (ρ / 2) * (N + 1 : ℕ) < dist p x := lt_of_not_ge hbound
  have hlevels (i : Fin (N + 2)) : ∃ y ∈ regularComponent g p (4 * δ),
      dist p y = (ρ / 2) * (i : ℕ) := by
    apply (isPreconnected_regularComponent g p (4 * δ)).intermediate_value hp hx
      (continuous_const.dist continuous_id).continuousOn
    constructor
    · simp only [id_eq, dist_self]
      positivity
    · have hi : (i : ℕ) ≤ N + 1 := by omega
      exact (mul_le_mul_of_nonneg_left (by exact_mod_cast hi)
        (by positivity : 0 ≤ ρ / 2)).trans hfar.le
  choose y hy hlevel using hlevels
  choose f hf using fun i : Fin (N + 2) => hcover (y i) (hy i)
  have hinj : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    by_contra hne
    have hsmall : dist (y i) (y j) ≤ ρ / 4 := by
      have hi := hf i
      have hj := hf j
      rw [← hij] at hj
      have htri := dist_triangle (y i) (C.centre (f i)) (y j)
      rw [dist_comm (C.centre (f i)) (y j)] at htri
      linarith
    have hcases : (i : ℕ) + 1 ≤ j ∨ (j : ℕ) + 1 ≤ i := by omega
    rcases hcases with hlt | hlt
    · have hlt' : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hlt
      have htri := dist_triangle p (y i) (y j)
      rw [hlevel i, hlevel j] at htri
      nlinarith
    · have hlt' : (j : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hlt
      have htri := dist_triangle p (y j) (y i)
      rw [hlevel i, hlevel j, dist_comm (y j) (y i)] at htri
      nlinarith
  have hcard := Fintype.card_le_of_injective f hinj
  simp only [Fintype.card_fin] at hcard
  omega



theorem chart_distance_le (C : RegularNormalChartCover g p δ R ρ N)
    (hdist : ∀ x y : M, edist x y = g.edist x y)
    (hρ : 0 < ρ) (hρR : 2 * ρ < R)
    (i : Fin (N + 1)) {w : EuclideanSpace ℝ (Fin n)}
    (hw : w ∈ ball 0 (ρ / 2)) :
    dist p (C.chart i w) ≤ (ρ / 2) * (N + 1 : ℕ) + ρ / 2 := by
  have hcentre := C.base_distance_le hdist hρ hρR (C.centre_mem i)
  have hwR : w ∈ ball 0 R := ball_subset_ball (by linarith : ρ / 2 ≤ R) hw
  have hradial : dist (C.centre i) (C.chart i w) = ‖w‖ := by
    rw [dist_edist, hdist, C.radial_distance i w hwR,
      ENNReal.toReal_ofReal (norm_nonneg _)]
  exact (dist_triangle p (C.centre i) (C.chart i w)).trans
    (add_le_add hcentre (hradial.le.trans (mem_ball_zero_iff.mp hw).le))

end PoincareConjecture.M28.RegularNormalChartCover
