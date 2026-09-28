import PoincareConjecture.Proofs.M04.ChartScalarBarrier
import PoincareConjecture.Proofs.M04.LocalScalarBarrier
import PoincareConjecture.Proofs.M04.ConnectedPropagation

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology Filter Metric

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
theorem ricciFlow_local_positive_transfer [T2Space M]
    {J : Set ℝ} {a b : ℝ} (hab : a < b) (F : RicciFlow n M J)
    (hJ : Icc a b ⊆ J) (f v : ℝ → M → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ univ))
    (hderiv : ∀ t ∈ Icc a b, ∀ x : M,
      HasDerivWithinAt (fun s ↦ f s x) (v t x) (Icc a b) t)
    (hsmooth : ∀ t ∈ Icc a b, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f t))
    (hnonneg : ∀ t ∈ Icc a b, ∀ x : M, 0 ≤ f t x)
    (hevol : ∀ t ∈ Ioc a b, ∀ x : M,
      (F.connection t).laplacian (f t) x ≤ v t x)
    (p : M) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∀ s t : ℝ, a ≤ s → s < t → t ≤ b → ∀ y ∈ U, ∀ z ∈ U,
        0 < f s y → 0 < f t z := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := extChartAt (𝓡 n) p
  obtain ⟨rho, hrho, htarget⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_extChartAt_target (I := 𝓡 n) p).mem_nhds (mem_extChartAt_target p))
  let R : ℝ := rho / 4
  have hR : 0 < R := by dsimp [R]; positivity
  have hball : closedBall (e p) (3 * R) ⊆ e.target :=
    (closedBall_subset_ball (by dsimp [R]; linarith)).trans htarget
  let U : Set M := e.source ∩ e ⁻¹' ball (e p) (R / 4)
  have hU : IsOpen U :=
    (continuousOn_extChartAt p).isOpen_inter_preimage
      (isOpen_extChartAt_source p) isOpen_ball
  refine ⟨U, hU, ⟨mem_extChartAt_source p, mem_ball_self (by positivity)⟩, ?_⟩
  intro s t has hst htb y hy z hz hpositive
  have hyS : y ∈ e.source := hy.1
  have hzS : z ∈ e.source := hz.1
  have hyR : dist (e y) (e p) < R / 4 := hy.2
  have hzR : dist (e z) (e p) < R / 4 := hz.2
  have hzy : ‖e z - e y‖ < R / 2 := by
    have h := dist_triangle (e z) (e p) (e y)
    rw [dist_comm (e p) (e y)] at h
    have hd : dist (e z) (e y) < R / 2 := by linarith
    simpa only [dist_eq_norm] using hd
  have hballY : closedBall (e y) R ⊆ e.target :=
    (closedBall_subset_closedBall' (by linarith : R + dist (e y) (e p) ≤ 3 * R)).trans hball
  let C : Set M := e.symm '' closedBall (e y) R
  obtain ⟨hC, hCU, hmem, hinterior⟩ := chart_closedBall_properties p (e y) hR hballY
  have hzC : z ∈ C := (hmem z hzS).2 (by linarith)
  have hstI : Icc s t ⊆ Icc a b := Icc_subset_Icc has htb
  have hs : s ∈ Icc a b := hstI ⟨le_rfl, hst.le⟩
  let epsilon : ℝ := f s y / 2
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have hcont : ContinuousAt (fun w : E ↦ f s (e.symm w)) (e y) :=
    (hsmooth s hs).continuous.continuousAt.comp (continuousAt_extChartAt_symm' hyS)
  have hseed : {w : E | epsilon < f s (e.symm w)} ∈ 𝓝 (e y) := by
    apply hcont.preimage_mem_nhds
    apply Ioi_mem_nhds
    rw [e.left_inv hyS]
    dsimp [epsilon]
    linarith
  obtain ⟨delta, hdelta, hseedBall⟩ := Metric.mem_nhds_iff.mp hseed
  let r : ℝ := min (R / 4) (delta / 2)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrR : r < R / 2 := by
    have h : r ≤ R / 4 := min_le_left _ _
    linarith
  have hrdelta : r < delta := by
    have h : r ≤ delta / 2 := min_le_right _ _
    linarith
  have hrsq : r ^ 2 < (R / 2) ^ 2 := (sq_lt_sq₀ hr.le (by positivity)).2 hrR
  let q : M → ℝ := fun x ↦ r ^ 2 - ‖e x - e y‖ ^ 2
  let speed : ℝ := ((R / 2) ^ 2 - r ^ 2) / (t - s)
  have hspeed : 0 < speed := div_pos (sub_pos.mpr hrsq) (sub_pos.mpr hst)
  have hspeedEnd : speed * (t - s) = (R / 2) ^ 2 - r ^ 2 :=
    div_mul_cancel₀ _ (sub_ne_zero.mpr hst.ne')
  have hq : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ q e.source :=
    contMDiffOn_chart_radial p (e y) r
  have hcritical : ∀ tau ∈ Icc s t, ∀ x ∈ C,
      q x + speed * (tau - s) = 0 → mfderiv (𝓡 n) 𝓘(ℝ, ℝ) q x ≠ 0 := by
    intro tau htau x hx hzero
    apply mfderiv_chart_radial_ne_zero p (e y) r (hCU hx)
    intro heq
    change e x = e y at heq
    have hqx : q x = r ^ 2 := by simp [q, heq]
    rw [hqx] at hzero
    have hmul : 0 ≤ speed * (tau - s) := mul_nonneg hspeed.le (sub_nonneg.mpr htau.1)
    nlinarith [sq_pos_of_pos hr]
  have hboundary : ∀ tau ∈ Icc s t, ∀ x ∈ C \ interior C,
      q x + speed * (tau - s) ≤ 0 := by
    intro tau htau x hx
    have hnorm : ‖e x - e y‖ = R := le_antisymm ((hmem x (hCU hx.1)).mp hx.1)
      (le_of_not_gt (fun hlt ↦ hx.2 (hinterior x (hCU hx.1) hlt)))
    have hmul : speed * (tau - s) ≤ speed * (t - s) :=
      mul_le_mul_of_nonneg_left (by linarith [htau.2]) hspeed.le
    change r ^ 2 - ‖e x - e y‖ ^ 2 + speed * (tau - s) ≤ 0
    rw [hnorm]
    nlinarith [sq_nonneg R]
  have hinit : ∀ x ∈ C, epsilon * expNegInvGlue (q x) ≤ f s x := by
    intro x hx
    by_cases hqx : q x ≤ 0
    · rw [expNegInvGlue.zero_of_nonpos hqx, mul_zero]
      exact hnonneg s hs x
    · have hpos : 0 < q x := lt_of_not_ge hqx
      have hsq : ‖e x - e y‖ ^ 2 < r ^ 2 := by
        dsimp [q] at hpos
        linarith
      have hnorm : ‖e x - e y‖ < r := (sq_lt_sq₀ (norm_nonneg _) hr.le).mp hsq
      have hseedx : epsilon ≤ f s x := by
        have h := hseedBall (mem_ball_iff_norm.mpr (hnorm.trans hrdelta))
        change epsilon < f s (e.symm (e x)) at h
        rw [e.left_inv (hCU hx)] at h
        exact h.le
      have hprofile : expNegInvGlue (q x) ≤ 1 := by
        rw [expNegInvGlue, if_neg hqx]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (inv_nonneg.mpr hpos.le))
      calc
        epsilon * expNegInvGlue (q x) ≤ epsilon * 1 :=
          mul_le_mul_of_nonneg_left hprofile hepsilon.le
        _ = epsilon := mul_one _
        _ ≤ f s x := hseedx
  obtain ⟨A, _, hbar⟩ := ricciFlow_compactDomain_moving_barrier hst F (hstI.trans hJ)
    (isOpen_extChartAt_source p) hC hCU hq hcritical f v
    (hf.mono (prod_mono hstI (subset_univ C)))
    (fun tau htau x _ ↦ (hderiv tau (hstI htau) x).mono hstI)
    (fun tau htau ↦ (hsmooth tau (hstI htau)).contMDiffOn)
    (fun tau htau x _ ↦ hnonneg tau (hstI htau) x)
    (fun tau htau x _ ↦ hevol tau ⟨has.trans_lt htau.1, htau.2.trans htb⟩ x)
    hboundary
  have hcomparison := hbar epsilon hepsilon.le hinit t ⟨hst.le, le_rfl⟩ z hzC
  have hargument : 0 < q z + speed * (t - s) := by
    have hsq : ‖e z - e y‖ ^ 2 < (R / 2) ^ 2 :=
      (sq_lt_sq₀ (norm_nonneg _) (by positivity)).2 hzy
    dsimp [q]
    linarith
  exact (mul_pos (mul_pos hepsilon (Real.exp_pos _))
    (expNegInvGlue.pos_of_pos hargument)).trans_le hcomparison

theorem ricciFlow_supersolution_positive_at_later_time [T2Space M] [ConnectedSpace M]
    {J : Set ℝ} {a b : ℝ} (hab : a < b) (F : RicciFlow n M J)
    (hJ : Icc a b ⊆ J) (f v : ℝ → M → ℝ)
    (hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ univ))
    (hderiv : ∀ t ∈ Icc a b, ∀ x : M,
      HasDerivWithinAt (fun s ↦ f s x) (v t x) (Icc a b) t)
    (hsmooth : ∀ t ∈ Icc a b, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f t))
    (hnonneg : ∀ t ∈ Icc a b, ∀ x : M, 0 ≤ f t x)
    (hevol : ∀ t ∈ Ioc a b, ∀ x : M,
      (F.connection t).laplacian (f t) x ≤ v t x)
    (p : M) (hp : 0 < f a p) : ∀ x : M, 0 < f b x := by
  exact positive_everywhere_of_local_transfer hab f
    (fun t ht ↦ (hsmooth t ht).continuous)
    (ricciFlow_local_positive_transfer hab F hJ f v hf hderiv hsmooth hnonneg hevol) p hp

end PoincareConjecture.M04
