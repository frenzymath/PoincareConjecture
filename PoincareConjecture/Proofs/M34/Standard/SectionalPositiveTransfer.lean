import PoincareConjecture.Proofs.M34.Standard.SectionalMovingBarrier
import PoincareConjecture.Proofs.M04.ChartScalarBarrier
import PoincareConjecture.Proofs.M04.ConnectedPropagation










set_option autoImplicit false

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

open M04



theorem sectional_local_positive_transfer
    {J : Set ℝ} {a b : ℝ} (F : RicciFlow 3 (EuclideanSpace ℝ (Fin 3)) J)
    (hJ : Icc a b ⊆ J)
    (hnonneg : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (p : EuclideanSpace ℝ (Fin 3)) :
    ∃ U : Set (EuclideanSpace ℝ (Fin 3)), IsOpen U ∧ p ∈ U ∧
      ∀ s t : ℝ, a ≤ s → s < t → t ≤ b → ∀ y ∈ U, ∀ z ∈ U,
        0 < modelLeastSectional (F.connection s) y →
          0 < modelLeastSectional (F.connection t) z := by
  let E := EuclideanSpace ℝ (Fin 3)
  let f := fun t => modelLeastSectional (F.connection t)
  have hf0 (t : ℝ) (ht : t ∈ Icc a b) (x : E) : 0 ≤ f t x := by
    apply le_modelLeastSectional
    intro q hq
    exact div_nonneg (hnonneg t ht x q.1 q.2)
      (metricGram_pos_of_linearIndependent _ _ _ _
        (modelOrthonormalPairs_linearIndependent hq)).le
  refine ⟨ball p (1 / 4), isOpen_ball, mem_ball_self (by norm_num), ?_⟩
  intro s t has hst htb y hy z hz hpositive
  have hzy : ‖z - y‖ < (1 / 2 : ℝ) := by
    have h := dist_triangle z p y
    rw [dist_comm p y] at h
    have hy' : dist y p < 1 / 4 := hy
    have hz' : dist z p < 1 / 4 := hz
    rw [← dist_eq_norm]
    linarith
  let K : Set E := closedBall y 1
  have hzK : z ∈ K := mem_closedBall_iff_norm.mpr (by linarith)
  have hstI : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
  have hs : s ∈ Icc a b := hstI ⟨le_rfl, hst.le⟩
  let epsilon : ℝ := f s y / 2
  have hepsilon : 0 < epsilon := by dsimp only [epsilon, f]; positivity
  have hcont : ContinuousAt (f s) y :=
    (continuous_modelLeastSectional_slice F (hJ hs)).continuousAt
  have hseed : {x : E | epsilon < f s x} ∈ 𝓝 y := by
    apply hcont.preimage_mem_nhds
    apply Ioi_mem_nhds
    dsimp only [epsilon, f]
    linarith
  obtain ⟨delta, hdelta, hseedBall⟩ := Metric.mem_nhds_iff.mp hseed
  let r : ℝ := min (1 / 4) (delta / 2)
  have hr : 0 < r := lt_min (by norm_num) (by positivity)
  have hrR : r < 1 / 2 := (min_le_left _ _).trans_lt (by norm_num)
  have hrdelta : r < delta := (min_le_right _ _).trans_lt (by linarith)
  have hrsq : r ^ 2 < (1 / 2 : ℝ) ^ 2 := (sq_lt_sq₀ hr.le (by norm_num)).2 hrR
  let q := fun x : E => r ^ 2 - ‖x - y‖ ^ 2
  let speed := ((1 / 2 : ℝ) ^ 2 - r ^ 2) / (t - s)
  have hspeed : 0 < speed := div_pos (sub_pos.mpr hrsq) (sub_pos.mpr hst)
  have hspeedEnd : speed * (t - s) = (1 / 2 : ℝ) ^ 2 - r ^ 2 :=
    div_mul_cancel₀ _ (sub_ne_zero.mpr hst.ne')
  have hq : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ q :=
    (contDiff_const.sub ((contDiff_id.sub contDiff_const).norm_sq ℝ)).contMDiff
  have hcritical : ∀ tau ∈ Icc s t, ∀ x ∈ K,
      q x + speed * (tau - s) = 0 → mfderiv (𝓡 3) 𝓘(ℝ, ℝ) q x ≠ 0 := by
    intro tau htau x _hx hzero
    have hxne : x ≠ y := by
      intro hxy
      have hqx : q x = r ^ 2 := by simp [q, hxy]
      rw [hqx] at hzero
      have hmul := mul_nonneg hspeed.le (sub_nonneg.mpr htau.1)
      nlinarith [sq_pos_of_pos hr]
    have hxS : x ∈ (extChartAt (𝓡 3) (0 : E)).source := by
      rw [extChartAt_model_space_eq_id]
      exact mem_univ x
    have he (w : E) : extChartAt (𝓡 3) (0 : E) w = w := by
      rw [extChartAt_model_space_eq_id]
      rfl
    have h := mfderiv_chart_radial_ne_zero (0 : E) y r hxS (by
      simpa only [he] using hxne)
    have heq : (fun w : E => r ^ 2 - ‖extChartAt (𝓡 3) (0 : E) w - y‖ ^ 2) = q := by
      funext w
      rw [he]
    rw [heq] at h
    exact h
  have hboundary : ∀ tau ∈ Icc s t, ∀ x ∈ K \ interior K,
      q x + speed * (tau - s) ≤ 0 := by
    intro tau htau x hx
    have hnorm : ‖x - y‖ = 1 := le_antisymm (mem_closedBall_iff_norm.mp hx.1)
      (le_of_not_gt fun hlt => hx.2 (mem_interior.mpr
        ⟨ball y 1, ball_subset_closedBall, isOpen_ball, mem_ball_iff_norm.mpr hlt⟩))
    have hmul := mul_le_mul_of_nonneg_left (show tau - s ≤ t - s by linarith [htau.2])
      hspeed.le
    dsimp only [q]
    rw [hnorm]
    nlinarith
  have hinit : ∀ x ∈ K, epsilon * expNegInvGlue (q x) ≤ f s x := by
    intro x _hx
    by_cases hqx : q x ≤ 0
    · rw [expNegInvGlue.zero_of_nonpos hqx, mul_zero]
      exact hf0 s hs x
    · have hpos : 0 < q x := lt_of_not_ge hqx
      have hsq : ‖x - y‖ ^ 2 < r ^ 2 := by dsimp only [q] at hpos; linarith
      have hnorm : ‖x - y‖ < r := (sq_lt_sq₀ (norm_nonneg _) hr.le).mp hsq
      have hseedx : epsilon ≤ f s x :=
        (hseedBall (mem_ball_iff_norm.mpr (hnorm.trans hrdelta))).le
      have hprofile : expNegInvGlue (q x) ≤ 1 := by
        rw [expNegInvGlue, if_neg hqx]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (inv_nonneg.mpr hpos.le))
      exact (mul_le_mul_of_nonneg_left hprofile hepsilon.le).trans
        (by simpa only [mul_one] using hseedx)
  obtain ⟨A, _hA, hbar⟩ := sectional_compact_moving_barrier hst F (hstI.trans hJ)
    (isCompact_closedBall y 1) hq hcritical (fun tau htau => hnonneg tau (hstI htau))
    hboundary
  have hcomparison := hbar epsilon hepsilon.le hinit t ⟨hst.le, le_rfl⟩ z hzK
  have hargument : 0 < q z + speed * (t - s) := by
    have hsq := (sq_lt_sq₀ (norm_nonneg (z - y)) (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hzy
    dsimp only [q]
    linarith
  exact (mul_pos (mul_pos hepsilon (Real.exp_pos _))
    (expNegInvGlue.pos_of_pos hargument)).trans_le hcomparison



theorem modelLeastSectional_positive_later
    {J : Set ℝ} {a b : ℝ} (hab : a < b)
    (F : RicciFlow 3 (EuclideanSpace ℝ (Fin 3)) J) (hJ : Icc a b ⊆ J)
    (hnonneg : ∀ t ∈ Icc a b, (F.connection t).NonnegativeSectionalCurvature)
    (p : EuclideanSpace ℝ (Fin 3)) (hp : 0 < modelLeastSectional (F.connection a) p) :
    ∀ x, 0 < modelLeastSectional (F.connection b) x :=
  positive_everywhere_of_local_transfer hab (fun t => modelLeastSectional (F.connection t))
    (fun _t ht => continuous_modelLeastSectional_slice F (hJ ht))
    (sectional_local_positive_transfer F hJ hnonneg) p hp

end PoincareConjecture.M34
