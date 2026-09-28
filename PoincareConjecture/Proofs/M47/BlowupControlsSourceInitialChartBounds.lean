import PoincareConjecture.Proofs.M47.TerminalSourceChartsBuffers

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem source_initial_chart_closed_bounds
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    {tau K R rho a b : ℝ} (htau : 0 < tau) (hK : 0 ≤ K) (hrhoR : 2 * rho < R)
    (F : RicciFlow 3 M (Icc (-tau) 0))
    (Phi : PartialDiffeomorph (𝓡 3) (𝓡 3) E M ∞)
    (hcurv : ∀ s ∈ Icc (-tau) 0, ∀ y ∈ Phi '' Metric.ball 0 R,
      (F.connection s).curvatureTensorNorm y ≤ K)
    (hterminal : ∀ x ∈ Metric.closedBall (0 : E) (2 * rho), ∀ v,
      a * ‖v‖ ^ 2 ≤ (F.metric 0).pullbackCoefficients Phi x v v ∧
        (F.metric 0).pullbackCoefficients Phi x v v ≤ b * ‖v‖ ^ 2)
    {s : ℝ} (hs : s ∈ Icc (-tau) 0) {x : E}
    (hx : x ∈ Metric.closedBall 0 (2 * rho)) (v : E) :
    (a * Real.exp (-54 * K * tau)) * ‖v‖ ^ 2 ≤
        (F.metric s).pullbackCoefficients Phi x v v ∧
      (F.metric s).pullbackCoefficients Phi x v v ≤
        (b * Real.exp (54 * K * tau)) * ‖v‖ ^ 2 := by
  have hzero : (0 : ℝ) ∈ Icc (-tau) 0 := ⟨by linarith only [htau], le_rfl⟩
  let w := mfderiv (𝓡 3) (𝓡 3) Phi x v
  have hnonneg (t : ℝ) : 0 ≤ (F.metric t).inner (Phi x) w w := by
    by_cases hw : w = 0
    · simp only [hw, map_zero, le_refl]
    · exact ((F.metric t).pos (Phi x) w hw).le
  have hRic : ∀ t ∈ Icc (-tau) 0,
      |(F.connection t).ricci (Phi x) w w| ≤
        (27 * K) * (F.metric t).inner (Phi x) w w := by
    intro t ht
    have h := (F.connection t).abs_ricci_quadratic_le_curvatureTensorNorm (Phi x) w
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) (Phi x)) = 3 :=
      finrank_euclideanSpace_fin
    simp only [Fintype.card_fin, hdim] at h
    norm_num at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hcurv t ht _
        ⟨x, Metric.closedBall_subset_ball hrhoR hx, rfl⟩) (by norm_num)) (hnonneg t))
  have htime := F.metric_inner_self_exp_bounds (convex_Icc (-tau) 0) (Subset.refl _)
    (Phi x) w (27 * K) hRic hzero hs
  have hdist : |s - 0| ≤ tau := by
    rw [abs_le]
    constructor <;> linarith only [hs.1, hs.2]
  have hlo : Real.exp (-54 * K * tau) * (F.metric 0).pullbackCoefficients Phi x v v ≤
      (F.metric s).pullbackCoefficients Phi x v v := by
    apply le_trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (hnonneg 0)) htime.1
    nlinarith only [mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ 54 * K)]
  have hhi : (F.metric s).pullbackCoefficients Phi x v v ≤
      Real.exp (54 * K * tau) * (F.metric 0).pullbackCoefficients Phi x v v := by
    apply htime.2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (hnonneg 0))
    nlinarith only [mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ 54 * K)]
  have hb := hterminal x hx v
  constructor
  · calc
      _ = Real.exp (-54 * K * tau) * (a * ‖v‖ ^ 2) := by ring
      _ ≤ Real.exp (-54 * K * tau) * (F.metric 0).pullbackCoefficients Phi x v v :=
        mul_le_mul_of_nonneg_left hb.1 (Real.exp_pos _).le
      _ ≤ _ := hlo
  · apply hhi.trans
    calc
      _ ≤ Real.exp (54 * K * tau) * (b * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hb.2 (Real.exp_pos _).le
      _ = _ := by ring

end PoincareConjecture.M47
