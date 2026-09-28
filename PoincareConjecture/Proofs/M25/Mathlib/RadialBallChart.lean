import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.OpenPartialHomeomorph.Defs











set_option autoImplicit false

open Set Metric
open scoped ContDiff

namespace OpenPartialHomeomorph





theorem exists_smooth_radialBall_chart
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (tau : OpenPartialHomeomorph ℝ ℝ)
    {R S m n k : ℝ}
    (hR : 0 < R) (hS : 0 < S)
    (hm : 0 < m) (hmR : m < R)
    (hn : 0 < n) (hnS : n < S)
    (hsource : tau.source = Ioo (-R) R)
    (htarget : tau.target = Ioo (-S) S)
    (htau : ContDiffOn ℝ ∞ (tau : ℝ → ℝ) tau.source)
    (htaui : ContDiffOn ℝ ∞ tau.symm tau.target)
    (hmono : StrictMonoOn (tau : ℝ → ℝ) (Ioo (-R) R))
    (hzero : tau 0 = 0)
    (hcenter : ∀ r ∈ Icc 0 m,
      0 < 1 + k * r ^ 2 ∧
      tau r = r / Real.sqrt (1 + k * r ^ 2))
    (hicenter : ∀ r ∈ Icc 0 n,
      0 < 1 - k * r ^ 2 ∧
      tau.symm r = r / Real.sqrt (1 - k * r ^ 2)) :
    ∃ e : OpenPartialHomeomorph E E,
      e.source = ball 0 R ∧ e.target = ball 0 S ∧
      (e : E → E) = (fun x => (tau ‖x‖ / ‖x‖) • x) ∧
      (e.symm : E → E) = (fun y => (tau.symm ‖y‖ / ‖y‖) • y) ∧
      ContDiffOn ℝ ∞ (e : E → E) e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      e 0 = 0 ∧ e.symm 0 = 0 ∧
      (∀ x ∈ e.source, ‖e x‖ = tau ‖x‖) ∧
      (∀ y ∈ e.target, ‖e.symm y‖ = tau.symm ‖y‖) ∧
      EqOn (e : E → E)
        (fun x => (Real.sqrt (1 + k * ‖x‖ ^ 2))⁻¹ • x)
        (closedBall 0 m) ∧
      EqOn (e.symm : E → E)
        (fun y => (Real.sqrt (1 - k * ‖y‖ ^ 2))⁻¹ • y)
        (closedBall 0 n) ∧
      (∀ a ∈ Ico 0 R,
        e '' {x : E | a < ‖x‖ ∧ ‖x‖ < R} =
          {y : E | tau a < ‖y‖ ∧ ‖y‖ < S}) := by
  have hs0 : (0 : ℝ) ∈ Ioo (-R) R := ⟨neg_neg_of_pos hR, hR⟩
  have hi0 : tau.symm 0 = 0 := by
    have h := tau.left_inv (hsource.symm ▸ hs0)
    change tau.symm (tau 0) = 0 at h
    rw [hzero] at h
    exact h
  have hpos (r : ℝ) (hr : 0 < r) (hrR : r < R) : 0 < tau r := by
    rw [← hzero]
    exact hmono hs0 ⟨hs0.1.trans hr, hrR⟩ hr
  have hipos (r : ℝ) (hr : 0 < r) (hrS : r < S) : 0 < tau.symm r := by
    have hrmem : r ∈ tau.target := by rw [htarget]; constructor <;> linarith
    have himem : tau.symm r ∈ Ioo (-R) R := hsource ▸ tau.map_target hrmem
    by_contra h
    have hle := hmono.monotoneOn himem hs0 (le_of_not_gt h)
    rw [tau.right_inv hrmem, hzero] at hle
    exact not_le_of_gt hr hle
  have hnormR (x : E) (hx : x ∈ ball 0 R) : ‖x‖ ∈ Ioo (-R) R :=
    ⟨lt_of_lt_of_le hs0.1 (norm_nonneg x), mem_ball_zero_iff.mp hx⟩
  have hnormS (x : E) (hx : x ∈ ball 0 S) : ‖x‖ ∈ Ioo (-S) S :=
    ⟨lt_of_lt_of_le (neg_neg_of_pos hS) (norm_nonneg x), mem_ball_zero_iff.mp hx⟩
  let F : E → E := fun x => (tau ‖x‖ / ‖x‖) • x
  let G : E → E := fun y => (tau.symm ‖y‖ / ‖y‖) • y
  have hF0 : F 0 = 0 := by simp [F]
  have hG0 : G 0 = 0 := by simp [G]
  have hFnorm (x : E) (hx : x ∈ ball 0 R) : ‖F x‖ = tau ‖x‖ := by
    by_cases hx0 : x = 0
    · subst x; simp only [hF0, norm_zero, hzero]
    have hp := hpos ‖x‖ (norm_pos_iff.mpr hx0) (hnormR x hx).2
    change ‖(tau ‖x‖ / ‖x‖) • x‖ = _
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hp (norm_pos_iff.mpr hx0))]
    exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hx0)
  have hGnorm (y : E) (hy : y ∈ ball 0 S) : ‖G y‖ = tau.symm ‖y‖ := by
    by_cases hy0 : y = 0
    · subst y; simp only [hG0, norm_zero, hi0]
    have hp := hipos ‖y‖ (norm_pos_iff.mpr hy0) (hnormS y hy).2
    change ‖(tau.symm ‖y‖ / ‖y‖) • y‖ = _
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hp (norm_pos_iff.mpr hy0))]
    exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hy0)
  have hFmem (x : E) (hx : x ∈ ball 0 R) : F x ∈ ball 0 S := by
    rw [mem_ball_zero_iff, hFnorm x hx]
    exact (htarget ▸ tau.map_source (hsource.symm ▸ hnormR x hx)).2
  have hGmem (y : E) (hy : y ∈ ball 0 S) : G y ∈ ball 0 R := by
    rw [mem_ball_zero_iff, hGnorm y hy]
    exact (hsource ▸ tau.map_target (htarget.symm ▸ hnormS y hy)).2
  have hGF (x : E) (hx : x ∈ ball 0 R) : G (F x) = x := by
    by_cases hx0 : x = 0
    · subst x; rw [hF0, hG0]
    have hrne := norm_ne_zero_iff.mpr hx0
    have hsne := (hpos ‖x‖ (norm_pos_iff.mpr hx0) (hnormR x hx).2).ne'
    change (tau.symm ‖F x‖ / ‖F x‖) • ((tau ‖x‖ / ‖x‖) • x) = x
    rw [hFnorm x hx, tau.left_inv (hsource.symm ▸ hnormR x hx), smul_smul]
    have hmul : (‖x‖ / tau ‖x‖) * (tau ‖x‖ / ‖x‖) = 1 := by
      field_simp
    rw [hmul, one_smul]
  have hFG (y : E) (hy : y ∈ ball 0 S) : F (G y) = y := by
    by_cases hy0 : y = 0
    · subst y; rw [hG0, hF0]
    have hsne := norm_ne_zero_iff.mpr hy0
    have hrne := (hipos ‖y‖ (norm_pos_iff.mpr hy0) (hnormS y hy).2).ne'
    change (tau ‖G y‖ / ‖G y‖) • ((tau.symm ‖y‖ / ‖y‖) • y) = y
    rw [hGnorm y hy, tau.right_inv (htarget.symm ▸ hnormS y hy), smul_smul]
    have hmul : (‖y‖ / tau.symm ‖y‖) * (tau.symm ‖y‖ / ‖y‖) = 1 := by
      field_simp
    rw [hmul, one_smul]
  have hFc : EqOn F (fun x => (Real.sqrt (1 + k * ‖x‖ ^ 2))⁻¹ • x)
      (closedBall 0 m) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst x; simp only [hF0, smul_zero]
    have hc := hcenter ‖x‖ ⟨norm_nonneg x, mem_closedBall_zero_iff.mp hx⟩
    change (tau ‖x‖ / ‖x‖) • x = _
    rw [hc.2]
    congr 1
    field_simp [norm_ne_zero_iff.mpr hx0, Real.sqrt_ne_zero'.mpr hc.1]
  have hGc : EqOn G (fun y => (Real.sqrt (1 - k * ‖y‖ ^ 2))⁻¹ • y)
      (closedBall 0 n) := by
    intro y hy
    by_cases hy0 : y = 0
    · subst y; simp only [hG0, smul_zero]
    have hc := hicenter ‖y‖ ⟨norm_nonneg y, mem_closedBall_zero_iff.mp hy⟩
    change (tau.symm ‖y‖ / ‖y‖) • y = _
    rw [hc.2]
    congr 1
    field_simp [norm_ne_zero_iff.mpr hy0, Real.sqrt_ne_zero'.mpr hc.1]
  have hFcenter : ContDiffAt ℝ ∞ F 0 := by
    have hmodel : ContDiffAt ℝ ∞
        (fun x : E => (Real.sqrt (1 + k * ‖x‖ ^ 2))⁻¹ • x) 0 := by
      apply ContDiffAt.smul _ contDiffAt_id
      apply ContDiffAt.inv _ (by simp)
      apply ContDiffAt.sqrt _ (by simp)
      exact contDiffAt_const.add (contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt)
    apply hmodel.congr_of_eventuallyEq
    filter_upwards [closedBall_mem_nhds (0 : E) (lt_min hm (hm.trans hmR))] with x hx
    exact hFc (mem_closedBall_zero_iff.mpr
      ((mem_closedBall_zero_iff.mp hx).trans (min_le_left m R)))
  have hGcenter : ContDiffAt ℝ ∞ G 0 := by
    have hmodel : ContDiffAt ℝ ∞
        (fun y : E => (Real.sqrt (1 - k * ‖y‖ ^ 2))⁻¹ • y) 0 := by
      apply ContDiffAt.smul _ contDiffAt_id
      apply ContDiffAt.inv _ (by simp)
      apply ContDiffAt.sqrt _ (by simp)
      exact contDiffAt_const.sub (contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt)
    apply hmodel.congr_of_eventuallyEq
    filter_upwards [closedBall_mem_nhds (0 : E) (lt_min hn (hn.trans hnS))] with y hy
    exact hGc (mem_closedBall_zero_iff.mpr
      ((mem_closedBall_zero_iff.mp hy).trans (min_le_left n S)))
  have hFsmooth : ContDiffOn ℝ ∞ F (ball 0 R) := by
    intro x hx
    by_cases hx0 : x = 0
    · subst x; exact hFcenter.contDiffWithinAt
    apply ContDiffAt.contDiffWithinAt
    have hnorm : ContDiffAt ℝ ∞ (fun z : E => ‖z‖) x := contDiffAt_norm ℝ hx0
    have ht := htau.contDiffAt (tau.open_source.mem_nhds (hsource.symm ▸ hnormR x hx))
    exact ((ht.comp x hnorm).div hnorm (norm_ne_zero_iff.mpr hx0)).smul contDiffAt_id
  have hGsmooth : ContDiffOn ℝ ∞ G (ball 0 S) := by
    intro y hy
    by_cases hy0 : y = 0
    · subst y; exact hGcenter.contDiffWithinAt
    apply ContDiffAt.contDiffWithinAt
    have hnorm : ContDiffAt ℝ ∞ (fun z : E => ‖z‖) y := contDiffAt_norm ℝ hy0
    have ht := htaui.contDiffAt (tau.open_target.mem_nhds (htarget.symm ▸ hnormS y hy))
    exact ((ht.comp y hnorm).div hnorm (norm_ne_zero_iff.mpr hy0)).smul contDiffAt_id
  let e : OpenPartialHomeomorph E E :=
    { toFun := F
      invFun := G
      source := ball 0 R
      target := ball 0 S
      map_source' := hFmem
      map_target' := hGmem
      left_inv' := hGF
      right_inv' := hFG
      open_source := isOpen_ball
      open_target := isOpen_ball
      continuousOn_toFun := hFsmooth.continuousOn
      continuousOn_invFun := hGsmooth.continuousOn }
  refine ⟨e, rfl, rfl, rfl, rfl, hFsmooth, hGsmooth, hF0, hG0,
    hFnorm, hGnorm, hFc, hGc, ?_⟩
  intro a ha
  have hamem : a ∈ Ioo (-R) R := ⟨lt_of_lt_of_le hs0.1 ha.1, ha.2⟩
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    have hxb : x ∈ ball 0 R := mem_ball_zero_iff.mpr hx.2
    change tau a < ‖F x‖ ∧ ‖F x‖ < S
    refine ⟨?_, mem_ball_zero_iff.mp (hFmem x hxb)⟩
    rw [hFnorm x hxb]
    exact hmono hamem (hnormR x hxb) hx.1
  · intro y hy
    have hyb : y ∈ ball 0 S := mem_ball_zero_iff.mpr hy.2
    have hxb := hGmem y hyb
    have hinv : tau ‖G y‖ = ‖y‖ := by rw [← hFnorm (G y) hxb, hFG y hyb]
    refine ⟨G y, ⟨?_, mem_ball_zero_iff.mp hxb⟩, hFG y hyb⟩
    by_contra h
    have hle := hmono.monotoneOn (hnormR (G y) hxb) hamem (le_of_not_gt h)
    rw [hinv] at hle
    exact not_le_of_gt hy.1 hle

end OpenPartialHomeomorph
