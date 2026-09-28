import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerDiskComparison
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerEnergyDecay

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped ContDiff Topology ENNReal

noncomputable section

namespace PoincareConjecture.M60

open Poincare.Analysis.Sobolev.Weak

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem suL4_source_disk_bound {E : Type*} [NormedAddCommGroup E]
    {O : Set Plane} {f : Plane → E} (hf : MemLp f 4 (volume.restrict O))
    (a : Plane) {r : ℝ} (hr : 0 < r) (hsub : Metric.ball a r ⊆ O) :
    (∫ x in Metric.ball a r, ‖f x‖ ^ 2) ≤
      Real.sqrt Real.pi * r * Real.sqrt (∫ x in O, ‖f x‖ ^ 4) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball a r)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (measure_ball_lt_top : volume (Metric.ball a r) < ⊤)⟩
  have hfB := hf.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hs : MemLp (fun x => ‖f x‖ ^ 2) 2 (volume.restrict (Metric.ball a r)) := by
    have hdiv : (4 : ℝ≥0∞) / 2 = 2 := by
      rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, mul_div_assoc,
        ENNReal.div_self (by norm_num) (by norm_num), mul_one]
    simpa only [hdiv, ENNReal.toReal_ofNat, Real.rpow_two] using hfB.norm_rpow_div 2
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun x : Plane => sq_nonneg ‖f x‖)
    (Eventually.of_forall fun _ : Plane => (zero_le_one : (0 : ℝ) ≤ 1))
    (by simpa using hs) (memLp_const (μ := volume.restrict (Metric.ball a r)) (1 : ℝ))
  have hvol : volume.real (Metric.ball a r) = r ^ 2 * Real.pi := by
    simp only [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hr.le,
      ENNReal.toReal_ofReal Real.pi_pos.le]
  have hfour : (∫ x in Metric.ball a r, ‖f x‖ ^ 4) ≤ ∫ x in O, ‖f x‖ ^ 4 :=
    integral_mono_measure (Measure.restrict_mono hsub le_rfl)
      (Eventually.of_forall fun x => pow_nonneg (norm_nonneg _) _)
      (hf.integrable_norm_pow (by norm_num))
  have hCS' : (∫ x in Metric.ball a r, ‖f x‖ ^ 2) ≤
      Real.sqrt (∫ x in Metric.ball a r, ‖f x‖ ^ 4) *
        Real.sqrt (volume.real (Metric.ball a r)) := by
    simpa only [mul_one, Real.rpow_two, ← pow_mul, one_pow, integral_const,
      smul_eq_mul, mul_one, ← Real.sqrt_eq_rpow, Measure.real, Measure.restrict_apply_univ,
      show (2 : ℕ) * 2 = 4 from rfl] using hCS
  rw [hvol, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr.le] at hCS'
  calc
    _ ≤ Real.sqrt (∫ x in Metric.ball a r, ‖f x‖ ^ 4) * (r * Real.sqrt Real.pi) := hCS'
    _ ≤ Real.sqrt (∫ x in O, ‖f x‖ ^ 4) * (r * Real.sqrt Real.pi) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hfour) (by positivity)
    _ = _ := by ring

theorem suHessianTrace_le_residual {E : Type*} [NormedAddCommGroup E]
    {O : Set Plane} {H : Fin 2 → Fin 2 → Plane → E} {f : Plane → E}
    (hH : ∀ i j, MemLp (H i j) 2 (volume.restrict O))
    (hf : MemLp f 2 (volume.restrict O)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hres : ∀ᵐ x ∂volume.restrict O,
      ‖(∑ i : Fin 2, H i i x) - f x‖ ≤
        δ * Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2, ‖H i j x‖ ^ 2)) :
    (∫ x in O, ‖∑ i : Fin 2, H i i x‖ ^ 2) ≤
      2 * δ ^ 2 * suHessianEnergy H O + 2 * ∫ x in O, ‖f x‖ ^ 2 := by
  have ht := (memLp_finsetSum Finset.univ (fun i _ => hH i i)).norm.integrable_sq
  have he := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => (hH i j).norm.integrable_sq))
  have hf2 := hf.norm.integrable_sq
  have hle := integral_mono_ae ht ((he.const_mul (2 * δ ^ 2)).add (hf2.const_mul 2))
    (hres.mono fun x hx => by
      have he0 : 0 ≤ ∑ i : Fin 2, ∑ j : Fin 2, ‖H i j x‖ ^ 2 :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
      have hn := (norm_le_norm_sub_add (∑ i : Fin 2, H i i x) (f x)).trans
        (add_le_add hx le_rfl)
      have hn2 := (sq_le_sq₀ (norm_nonneg _)
        (add_nonneg (mul_nonneg hδ (Real.sqrt_nonneg _)) (norm_nonneg _))).mpr hn
      have hs := Real.sq_sqrt he0
      have hscale : (δ * Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2, ‖H i j x‖ ^ 2)) ^ 2 =
          δ ^ 2 * (∑ i : Fin 2, ∑ j : Fin 2, ‖H i j x‖ ^ 2) := by rw [mul_pow, hs]
      dsimp only [Pi.add_apply]
      nlinarith [sq_nonneg (δ * Real.sqrt (∑ i : Fin 2, ∑ j : Fin 2, ‖H i j x‖ ^ 2) -
        ‖f x‖)])
  simpa only [Pi.add_apply, integral_add (he.const_mul (2 * δ ^ 2)) (hf2.const_mul 2),
    integral_const_mul, suHessianEnergy] using hle

end PoincareConjecture.M60

end
