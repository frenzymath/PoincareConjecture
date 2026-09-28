import PoincareConjecture.Proofs.M07.Analysis.Calculus.Diffeomorphism.Perturbation
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set Filter Metric Poincare.Analysis.Calculus
open scoped ContDiff Topology

namespace PoincareConjecture.CapRecut

noncomputable def axialCutoff (A : ℝ) (hA : 0 < A) : ContDiffBump A where
  rIn := A / 8
  rOut := A / 4
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

theorem axialCutoff_eq_zero {A : ℝ} (hA : 0 < A) {x : ℝ} (hx : x ≤ A / 2) :
    axialCutoff A hA x = 0 := by
  apply (axialCutoff A hA).zero_of_le_dist
  change A / 4 ≤ dist x A
  rw [Real.dist_eq, abs_of_nonpos (by linarith : x - A ≤ 0)]
  linarith

theorem axialCutoff_at_endpoint {A : ℝ} (hA : 0 < A) :
    axialCutoff A hA A = 1 :=
  (axialCutoff A hA).one_of_mem_closedBall
    (mem_closedBall_self (axialCutoff A hA).rIn_pos.le)

theorem eventually_exists_axial_compression {A : ℝ} (hA : 0 < A)
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (hδpos : ∀ᶠ k in atTop, 0 < δ k) :
    ∀ᶠ k in atTop, A / 2 < A - δ k ∧ A - δ k < A ∧
      ∃ e : ℝ ≃ₜ ℝ, ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧ StrictMono e ∧
        (∀ x, e x = x - δ k * axialCutoff A hA x) ∧
        (∀ x, x ≤ A / 2 → e x = x) ∧
        e '' Ioo (-A) A = Ioo (-A) (A - δ k) := by
  let χ := axialCutoff A hA
  have hzero : TendstoUniformlyOn (fun k (x : ℝ) => x - δ k) id atTop (tsupport χ) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have hnorm : Tendsto (fun k => ‖δ k‖) atTop (𝓝 0) := by simpa using hδ.norm
    filter_upwards [(tendsto_order.mp hnorm).2 ε hε] with k hk x _
    simpa [Real.dist_eq] using hk
  have hone : TendstoUniformlyOn (fun k => fderiv ℝ (fun x : ℝ => x - δ k))
      (fun _ => ContinuousLinearMap.id ℝ ℝ) atTop (tsupport χ) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    exact Eventually.of_forall fun k x _ => by simpa only
      [fderiv_sub_const, fderiv_fun_id, dist_self] using hε
  have hsmooth : ∀ᶠ k in atTop, ∀ x ∈ tsupport χ,
      ContDiffAt ℝ ∞ (fun y : ℝ => y - δ k) x :=
    Eventually.of_forall fun k x _ => (contDiff_id.sub contDiff_const).contDiffAt
  filter_upwards [eventually_exists_cutoff_diffeomorphism_of_contDiffAt
    χ.contDiff χ.hasCompactSupport hsmooth hzero hone,
    hδpos, (tendsto_order.mp hδ).2 (A / 2) (by positivity)] with k hk hkpos hksmall
  obtain ⟨e, he, hes, hei, _, _⟩ := hk
  have hformula (x : ℝ) : e x = x - δ k * χ x := by
    rw [he]
    simp only [smul_eq_mul]
    ring
  have hfix (x : ℝ) (hx : x ≤ A / 2) : e x = x := by
    rw [hformula, axialCutoff_eq_zero hA hx, mul_zero, sub_zero]
  have hmono : StrictMono e := by
    rcases e.continuous.strictMono_of_inj e.injective with h | h
    · exact h
    · have hbad := h (show -A < (0 : ℝ) by linarith)
      rw [hfix _ (by linarith), hfix _ (by linarith)] at hbad
      linarith
  refine ⟨by linarith, by linarith, e, hes, hei, hmono, hformula, hfix, ?_⟩
  rw [e.continuous.image_Ioo_of_strictMono hmono, hfix _ (by linarith),
    hformula, axialCutoff_at_endpoint hA, mul_one]

theorem axial_perturbation_jets_tendsto {A : ℝ} (hA : 0 < A)
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (m : ℕ) :
    TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (fun x : ℝ => x - δ k * axialCutoff A hA x))
      (iteratedFDeriv ℝ m (id : ℝ → ℝ)) atTop univ := by
  let χ := axialCutoff A hA
  have hχ : ContDiff ℝ m χ := χ.contDiff
  obtain ⟨B, hB⟩ := (χ.hasCompactSupport.iteratedFDeriv (𝕜 := ℝ) m).exists_bound_of_continuous
    hχ.continuous_iteratedFDeriv'
  have hnorm : Tendsto (fun k => ‖δ k‖) atTop (𝓝 0) := by simpa using hδ.norm
  have hscale : Tendsto (fun k => ‖δ k‖ * (max B 0 + 1)) atTop (𝓝 0) := by
    simpa using hnorm.mul_const (max B 0 + 1)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp hscale).2 ε hε] with k hk x _
  have hjet : iteratedFDeriv ℝ m (fun y : ℝ => y - δ k * χ y) x =
      iteratedFDeriv ℝ m (id : ℝ → ℝ) x - δ k • iteratedFDeriv ℝ m χ x := by
    have hsub := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := m) (x := x)
      (f := id) contDiffAt_id (hχ.const_smul (δ k)).contDiffAt
    change iteratedFDeriv ℝ m (fun y : ℝ => y - δ k * χ y) x =
      iteratedFDeriv ℝ m (id : ℝ → ℝ) x -
        iteratedFDeriv ℝ m (fun y => δ k • χ y) x at hsub
    rw [iteratedFDeriv_const_smul_apply' hχ.contDiffAt] at hsub
    exact hsub
  rw [hjet, dist_comm, dist_self_sub_left, norm_smul]
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left ((hB x).trans (by linarith [le_max_left B 0])) (norm_nonneg _)) hk

end PoincareConjecture.CapRecut
