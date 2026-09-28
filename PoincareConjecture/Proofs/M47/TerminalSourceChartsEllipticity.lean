import PoincareConjecture.Proofs.M47.TerminalSourceCharts
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricComparison
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.NormBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable def terminalSourceLower (H τ : ℝ) : ℝ := Real.exp (-54 * H * τ) / 4
noncomputable def terminalSourceUpper (H τ : ℝ) : ℝ := 9 * Real.exp (54 * H * τ) / 4

theorem terminalSourceLower_pos (H τ : ℝ) : 0 < terminalSourceLower H τ := by
  unfold terminalSourceLower
  positivity

theorem terminalSourceUpper_pos (H τ : ℝ) : 0 < terminalSourceUpper H τ := by
  unfold terminalSourceUpper
  positivity

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M]

theorem TerminalSourceChart.closed_bounds {τ R H ρ : ℝ} (hτ : 0 < τ) (hH : 0 ≤ H)
    (F : RicciFlow 3 M (Icc (-τ) 0)) (C : TerminalSourceChart (F.metric 0) R)
    (hρR : 2 * ρ < R)
    (hsmall : ∀ s : ℝ, |s| ≤ 2 * ρ →
      (H * s ^ 2) * Real.exp (max 1 (H * s ^ 2)) ≤ 3)
    (hcurv : ∀ t ∈ Icc (-τ) 0, ∀ y ∈ C.chart '' Metric.ball 0 R,
      (F.connection t).curvatureTensorNorm y ≤ H)
    {t : ℝ} (ht : t ∈ Icc (-τ) 0) {x : E}
    (hx : x ∈ Metric.closedBall 0 (2 * ρ)) (v : E) :
    terminalSourceLower H τ * ‖v‖ ^ 2 ≤ (F.metric t).pullbackCoefficients C.chart x v v ∧
      (F.metric t).pullbackCoefficients C.chart x v v ≤ terminalSourceUpper H τ * ‖v‖ ^ 2 := by
  have h0 : (0 : ℝ) ∈ Icc (-τ) 0 := ⟨by linarith, le_rfl⟩
  have hb := C.terminal_bounds (F.connection 0) hρR hsmall (hcurv 0 h0) hx v
  let w := mfderiv (𝓡 3) (𝓡 3) C.chart x v
  have hnonneg (s : ℝ) : 0 ≤ (F.metric s).inner (C.chart x) w w := by
    by_cases hw : w = 0
    · simp [hw]
    · exact ((F.metric s).pos _ _ hw).le
  have hRic : ∀ s ∈ Icc (-τ) 0,
      |(F.connection s).ricci (C.chart x) w w| ≤ (27 * H) * (F.metric s).inner (C.chart x) w w := by
    intro s hs
    have h := (F.connection s).abs_ricci_quadratic_le_curvatureTensorNorm (C.chart x) w
    have hdim : Module.finrank ℝ (TangentSpace (𝓡 3) (C.chart x)) = 3 :=
      finrank_euclideanSpace_fin
    simp only [Fintype.card_fin, hdim] at h
    norm_num at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hcurv s hs _
        ⟨x, Metric.closedBall_subset_ball hρR hx, rfl⟩) (by norm_num)) (hnonneg s))
  have htime := F.metric_inner_self_exp_bounds (convex_Icc (-τ) 0) (Subset.refl _)
    (C.chart x) w (27 * H) hRic h0 ht
  have htau : |t - 0| ≤ τ := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hlo : Real.exp (-54 * H * τ) * (F.metric 0).pullbackCoefficients C.chart x v v ≤
      (F.metric t).pullbackCoefficients C.chart x v v := by
    apply le_trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (hnonneg 0)) htime.1
    nlinarith [mul_le_mul_of_nonneg_left htau (by positivity : 0 ≤ 54 * H)]
  have hhi : (F.metric t).pullbackCoefficients C.chart x v v ≤
      Real.exp (54 * H * τ) * (F.metric 0).pullbackCoefficients C.chart x v v := by
    apply htime.2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (hnonneg 0))
    nlinarith [mul_le_mul_of_nonneg_left htau (by positivity : 0 ≤ 54 * H)]
  constructor
  · calc
      _ = Real.exp (-54 * H * τ) * ((1 / 4 : ℝ) * ‖v‖ ^ 2) := by
        unfold terminalSourceLower
        ring
      _ ≤ Real.exp (-54 * H * τ) * (F.metric 0).pullbackCoefficients C.chart x v v :=
        mul_le_mul_of_nonneg_left hb.1 (Real.exp_pos _).le
      _ ≤ _ := hlo
  · apply hhi.trans
    calc
      _ ≤ Real.exp (54 * H * τ) * ((9 / 4 : ℝ) * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hb.2 (Real.exp_pos _).le
      _ = _ := by unfold terminalSourceUpper; ring

end PoincareConjecture.M47
