import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Statement
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.PointPicking
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.Scalar.SharpBounds

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

private theorem exists_selected_point_in_ball
    {X : Type*} [PseudoMetricSpace X]
    (R : X → ℝ) (hR : ∀ y, 0 ≤ R y) (hbounded : BddAbove (range R))
    (p x : X) {r : ℝ} (hr : 0 < r) (hx : x ∈ Metric.ball p r)
    (hRx : 0 < R x) :
    ∃ q : X, ∃ s : ℝ, q ∈ Metric.ball p (2 * r) ∧
      0 < s ∧ s ≤ r ∧ R x ≤ R q ∧
      s * Real.sqrt (R q) = r * Real.sqrt (R x) / 2 ∧
      Metric.ball q s ⊆ Metric.ball p (2 * r) ∧
      ∀ y ∈ Metric.ball q s, R y ≤ 4 * R q := by
  let f : X → ℝ := fun y => Real.sqrt (R y)
  let L : ℝ := r * f x / 2
  have hfx : 0 < f x := Real.sqrt_pos.mpr hRx
  have hL : 0 < L := by dsimp [L]; positivity
  have hbound : BddAbove (f '' (univ : Set X)) := by
    obtain ⟨B, hB⟩ := hbounded
    refine ⟨Real.sqrt B, ?_⟩
    rintro _ ⟨y, _, rfl⟩
    exact Real.sqrt_le_sqrt (hB (mem_range_self y))
  obtain ⟨q, _, _, hscore, hmargin, hcontrol⟩ :=
    Poincare.Parabolic.exists_point_with_doubling_bound univ f (dist x)
      (fun _ => 0) hbound hL.le (mem_univ x) hfx
  have hfq : 0 < f q := hfx.trans_le hscore
  let s : ℝ := L / f q
  have hs : 0 < s := div_pos hL hfq
  have hbudget : dist x q + 2 * s ≤ r := by
    have hcancel : 2 * L / f x = r := by
      dsimp [L]
      field_simp
    simpa only [dist_self, zero_add, hcancel, mul_div_assoc] using hmargin
  have hpx : dist p x < r := by simpa [dist_comm] using Metric.mem_ball.mp hx
  have hq : q ∈ Metric.ball p (2 * r) := by
    rw [Metric.mem_ball, dist_comm]
    linarith [dist_triangle p x q]
  refine ⟨q, s, hq, hs, ?_, ?_, ?_, ?_, ?_⟩
  · linarith [dist_nonneg (x := x) (y := q)]
  · exact (Real.sqrt_le_sqrt_iff (hR q)).mp hscore
  · dsimp [s, L]
    rw [div_mul_cancel₀ _ hfq.ne']
  · intro y hy
    have hqy : dist q y < s := by simpa [dist_comm] using Metric.mem_ball.mp hy
    rw [Metric.mem_ball, dist_comm]
    linarith [dist_triangle p x q, dist_triangle p q y]
  · intro y hy
    have hqy : dist q y < s := by simpa [dist_comm] using Metric.mem_ball.mp hy
    have hfy : f y ≤ 2 * f q := hcontrol y (mem_univ y) le_rfl (by
      have htri := dist_triangle x q y
      dsimp [s] at hqy
      linarith)
    have hsq := mul_self_le_mul_self (Real.sqrt_nonneg (R y)) hfy
    dsimp [f] at hsq
    nlinarith [Real.sq_sqrt (hR y), Real.sq_sqrt (hR q)]

variable {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem m23_exists_backward_controlled_point_in_ball
    (P : M23NormalizedKappaCompactnessPredecessors) (K : AncientKappaSolution 3 M)
    (p x : M) {r : ℝ} (hr : 0 < r) (hx : x ∈ (K.flow.metric 0).ball p r) :
    ∃ q : M, ∃ s : ℝ, q ∈ (K.flow.metric 0).ball p (2 * r) ∧
      0 < s ∧ s ≤ r ∧
      (K.flow.connection 0).scalarCurvature x ≤ (K.flow.connection 0).scalarCurvature q ∧
      s * Real.sqrt ((K.flow.connection 0).scalarCurvature q) =
        r * Real.sqrt ((K.flow.connection 0).scalarCurvature x) / 2 ∧
      (K.flow.metric 0).ball q s ⊆ (K.flow.metric 0).ball p (2 * r) ∧
      (∀ y ∈ (K.flow.metric 0).ball q s,
        (K.flow.connection 0).scalarCurvature y ≤ 4 * (K.flow.connection 0).scalarCurvature q) ∧
      ∀ t : ℝ, t ≤ 0 → ∀ y ∈ (K.flow.metric 0).ball q s,
        |(K.flow.connection t).curvatureTensorNorm y| ≤
          4 * (K.flow.connection 0).scalarCurvature q := by
  let g := K.flow.metric 0
  let R := (K.flow.connection 0).scalarCurvature
  let := g.toMetricSpace
  have hR (y : M) : 0 ≤ R y := (P.scalar_pos M K 0 le_rfl y).le
  have hbounded : BddAbove (range R) := by
    obtain ⟨B, _, hB⟩ := K.bounded_curvature 0 le_rfl
    refine ⟨3 * B, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact ((K.flow.connection 0).scalarCurvature_le_curvatureTensorNorm_sharp y).trans
      (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hB y)) (by norm_num))
  obtain ⟨q, s, hq, hs, hsr, hRq, hscale, hsubset, hcontrol⟩ :=
    exists_selected_point_in_ball R hR hbounded p x hr
      (by simpa only [g.toMetricSpace_ball] using hx) (P.scalar_pos M K 0 le_rfl x)
  simp only [g.toMetricSpace_ball] at hq hsubset hcontrol
  refine ⟨q, s, hq, hs, hsr, hRq, hscale, hsubset, hcontrol, ?_⟩
  intro t ht y hy
  rw [abs_of_nonneg (show 0 ≤ (K.flow.connection t).curvatureTensorNorm y from
    Real.sqrt_nonneg _)]
  exact (P.past_norm_le_scalar M K t 0 ht le_rfl y).trans (hcontrol y hy)

end PoincareConjecture
