import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Sequences
import Mathlib.Tactic













set_option autoImplicit false

open Filter Topology
open scoped BigOperators ContDiff

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

set_option backward.isDefEq.respectTransparency false in
theorem exists_smooth_upper_support_of_bounded_jets
    (f : E → ℝ)
    (c b : ℕ → ℝ)
    (A : ℕ → E →L[ℝ] ℝ)
    (H : ℕ → E →L[ℝ] E →L[ℝ] ℝ)
    (ρ C M Λ : ℝ)
    (hρ : 0 < ρ)
    (hC : 0 ≤ C)
    (hc : Tendsto c atTop (𝓝 (f 0)))
    (hb : Tendsto b atTop (𝓝 Λ))
    (hA : ∀ j, ‖A j‖ ≤ 1)
    (hH : ∀ j, ‖H j‖ ≤ M)
    (hHsym : ∀ j v w, H j v w = H j w v)
    (htrace : ∀ j, ∑ i, H j (e i) (e i) ≤ b j)
    (hmajor : ∀ j x, ‖x‖ < ρ →
      f x ≤ c j + A j x + (1 / 2 : ℝ) * H j x x + C * ‖x‖ ^ 3)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (P : E → ℝ) (r : ℝ),
      0 < r ∧ r ≤ ρ ∧
      ContDiff ℝ ∞ P ∧
      P 0 = f 0 ∧
      (∀ x, ‖x‖ < r → f x ≤ P x) ∧
      ‖fderiv ℝ P 0‖ ≤ 1 ∧
      (∑ i, fderiv ℝ (fderiv ℝ P) 0 (e i) (e i)) ≤ Λ + ε := by
  classical
  letI : FiniteDimensional ℝ (E →L[ℝ] ℝ) :=
    ContinuousLinearMap.finiteDimensional
  letI : FiniteDimensional ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.finiteDimensional
  letI : ProperSpace (E →L[ℝ] ℝ) :=
    FiniteDimensional.proper ℝ (E →L[ℝ] ℝ)
  letI : ProperSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
    FiniteDimensional.proper ℝ (E →L[ℝ] E →L[ℝ] ℝ)
  have hcompact : IsCompact
      (Metric.closedBall (0 : E →L[ℝ] ℝ) 1 ×ˢ
        Metric.closedBall (0 : E →L[ℝ] E →L[ℝ] ℝ) M) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  have hmem (j : ℕ) : (A j, H j) ∈
      Metric.closedBall (0 : E →L[ℝ] ℝ) 1 ×ˢ
        Metric.closedBall (0 : E →L[ℝ] E →L[ℝ] ℝ) M := by
    constructor
    · simpa only [Metric.mem_closedBall, dist_zero_right] using hA j
    · simpa +instances only [Metric.mem_closedBall] using!
        (dist_zero_right (H j)).le.trans (hH j)
  obtain ⟨⟨a, B⟩, hab, σ, hσ, hlim⟩ := hcompact.tendsto_subseq hmem
  have ha : ‖a‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hab.1
  have hAlim : Tendsto (fun j => A (σ j)) atTop (𝓝 a) :=
    (continuous_fst.tendsto (a, B)).comp hlim
  have hBlim : Tendsto (fun j => H (σ j)) atTop (𝓝 B) :=
    (continuous_snd.tendsto (a, B)).comp hlim
  have hAEval (x : E) : Tendsto (fun j => A (σ j) x) atTop (𝓝 (a x)) := by
    have hcont : Continuous (fun l : E →L[ℝ] ℝ => l x) :=
      continuous_id.clm_apply continuous_const
    exact (hcont.tendsto a).comp hAlim
  have hBEval (v w : E) :
      Tendsto (fun j => H (σ j) v w) atTop (𝓝 (B v w)) := by
    have hcont : Continuous (fun Q : E →L[ℝ] E →L[ℝ] ℝ => Q v w) :=
      (continuous_id.clm_apply continuous_const).clm_apply continuous_const
    exact (hcont.tendsto B).comp hBlim
  have hBsym (v w : E) : B v w = B w v := by
    apply le_antisymm
    · exact le_of_tendsto_of_tendsto' (hBEval v w) (hBEval w v)
        (fun j => (hHsym (σ j) v w).le)
    · exact le_of_tendsto_of_tendsto' (hBEval w v) (hBEval v w)
        (fun j => (hHsym (σ j) w v).le)
  have hBtrace : (∑ i, B (e i) (e i)) ≤ Λ := by
    have ht : Tendsto (fun j => ∑ i, H (σ j) (e i) (e i))
        atTop (𝓝 (∑ i, B (e i) (e i))) :=
      tendsto_finsetSum Finset.univ (fun i _ => hBEval (e i) (e i))
    exact le_of_tendsto_of_tendsto' ht (hb.comp hσ.tendsto_atTop)
      (fun j => htrace (σ j))

  have hmajor' (x : E) (hx : ‖x‖ < ρ) :
      f x ≤ f 0 + a x + (1 / 2 : ℝ) * B x x + C * ‖x‖ ^ 3 := by
    have ht : Tendsto
        (fun j => c (σ j) + A (σ j) x +
          (1 / 2 : ℝ) * H (σ j) x x + C * ‖x‖ ^ 3)
        atTop (𝓝 (f 0 + a x + (1 / 2 : ℝ) * B x x + C * ‖x‖ ^ 3)) :=
      (((hc.comp hσ.tendsto_atTop).add (hAEval x)).add
        (tendsto_const_nhds.mul (hBEval x x))).add tendsto_const_nhds
    exact le_of_tendsto_of_tendsto' tendsto_const_nhds ht
      (fun j => hmajor (σ j) x hx)
  let μ : ℝ := ε / (2 * ((n : ℝ) + 1))
  have hμ : 0 < μ := by
    dsimp [μ]
    positivity
  have hC1 : 0 < C + 1 := by linarith
  let r : ℝ := min (ρ / 2) (μ / (C + 1))
  have hr : 0 < r := lt_min (by positivity) (div_pos hμ hC1)
  have hrρ : r ≤ ρ := (min_le_left _ _).trans (by linarith)
  let J : E →L[ℝ] E →L[ℝ] ℝ :=
    LinearMap.mkContinuous₂ (innerₗ E) 1 (fun v w => by
      simpa only [innerₗ_apply_apply, one_mul] using norm_inner_le_norm v w)
  have hJ (v w : E) : J v w = inner ℝ v w := rfl
  let Q : E →L[ℝ] E →L[ℝ] ℝ :=
    B + (2 * μ) • J
  have hQsym (v w : E) : Q v w = Q w v := by
    simp only [Q, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, hJ]
    rw [hBsym v w, real_inner_comm v w]
  let P : E → ℝ := fun x => f 0 + a x + (1 / 2 : ℝ) * Q x x
  have hPcont : ContDiff ℝ ∞ P := by
    exact (contDiff_const.add a.contDiff).add
      (contDiff_const.mul (Q.contDiff.clm_apply contDiff_id))
  have hPmajor (x : E) (hx : ‖x‖ < r) : f x ≤ P x := by
    have hxρ : ‖x‖ < ρ := hx.trans_le hrρ
    have hxn : ‖x‖ ≤ μ / (C + 1) := hx.le.trans (min_le_right _ _)
    have hxn' : ‖x‖ * (C + 1) ≤ μ := (le_div_iff₀ hC1).mp hxn
    have hCxn : C * ‖x‖ ≤ μ := by nlinarith only [hxn', norm_nonneg x]
    have hcubic : C * ‖x‖ ^ 3 ≤ μ * ‖x‖ ^ 2 := by
      calc
        C * ‖x‖ ^ 3 = (C * ‖x‖) * ‖x‖ ^ 2 := by ring
        _ ≤ μ * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right hCxn (sq_nonneg _)
    calc
      f x ≤ f 0 + a x + (1 / 2 : ℝ) * B x x + C * ‖x‖ ^ 3 :=
        hmajor' x hxρ
      _ ≤ f 0 + a x + (1 / 2 : ℝ) * B x x + μ * ‖x‖ ^ 2 :=
        add_le_add_right hcubic _
      _ = P x := by
        simp only [P, Q, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          smul_eq_mul, hJ, real_inner_self_eq_norm_sq]
        ring
  have hdiag (x : E) :
      HasFDerivAt (fun y : E => (1 / 2 : ℝ) * Q y y) (Q x) x := by
    have hd := (Q.hasFDerivAt_of_bilinear
      (hasFDerivAt_id x) (hasFDerivAt_id x)).const_smul (1 / 2 : ℝ)
    have heq : (1 / 2 : ℝ) •
        (Q.precompR E x (ContinuousLinearMap.id ℝ E) +
          Q.precompL E (ContinuousLinearMap.id ℝ E) x) = Q x := by
      ext v
      change (1 / 2 : ℝ) * (Q x v + Q v x) = Q x v
      rw [hQsym v x]
      ring
    simp only [id_eq] at hd
    rw [heq] at hd
    simpa +instances only [Pi.smul_apply, smul_eq_mul] using! hd
  have hPderiv (x : E) : HasFDerivAt P (a + Q x) x := by
    simpa +instances only [P, Pi.add_apply, zero_add] using!
      ((hasFDerivAt_const (f 0) x).add a.hasFDerivAt).add (hdiag x)
  have hPf : fderiv ℝ P = fun x => a + Q x :=
    funext fun x => (hPderiv x).fderiv
  have hPf0 : fderiv ℝ P 0 = a := by
    rw [hPf]
    simp
  have hPsecond : fderiv ℝ (fderiv ℝ P) 0 = Q := by
    rw [hPf]
    exact (Q.hasFDerivAt.const_add a).fderiv
  have hQtrace : (∑ i, Q (e i) (e i)) =
      (∑ i, B (e i) (e i)) + (2 * μ) * (n : ℝ) := by
    simp only [Q, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, hJ, OrthonormalBasis.inner_eq_one, mul_one,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  have hμeq : μ * (2 * ((n : ℝ) + 1)) = ε := by
    dsimp [μ]
    exact div_mul_cancel₀ ε (by positivity)
  have hμtrace : (2 * μ) * (n : ℝ) ≤ ε := by
    nlinarith only [hμ.le, hμeq]
  refine ⟨P, r, hr, hrρ, hPcont, ?_, hPmajor, ?_, ?_⟩
  · simp [P]
  · simpa only [hPf0] using ha
  · rw [hPsecond, hQtrace]
    exact add_le_add hBtrace hμtrace

end PoincareConjecture.RicciFlowAnalysis
