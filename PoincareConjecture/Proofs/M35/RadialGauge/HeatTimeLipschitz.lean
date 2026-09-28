import PoincareConjecture.Proofs.M35.RadialGauge.HeatEquation
import Mathlib.Analysis.Calculus.MeanValue











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))


theorem euclidean_hessian_trace_norm_le (A : V →L[ℝ] V →L[ℝ] F) :
    ‖∑ i : Fin (n + 1), A (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ))‖ ≤ (n + 1) * ‖A‖ := by
  calc
    _ ≤ ∑ i : Fin (n + 1), ‖A (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single i (1 : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin (n + 1), ‖A‖ := by
      apply Finset.sum_le_sum
      intro i _
      have h1 := A.le_opNorm (EuclideanSpace.single i (1 : ℝ))
      have h2 := (A (EuclideanSpace.single i (1 : ℝ))).le_opNorm
        (EuclideanSpace.single i (1 : ℝ))
      simp only [EuclideanSpace.single, PiLp.norm_single, norm_one, mul_one] at h1 h2
      exact h2.trans h1
    _ = _ := by simp [Nat.cast_add, Nat.cast_one]



theorem heatAverage_time_lipschitz {f : V → F} {f' : V → V →L[ℝ] F}
    {f'' : V → V →L[ℝ] V →L[ℝ] F}
    (hf : Continuous f) (hf' : Continuous f') (hf'' : Continuous f'')
    (hd : ∀ x, HasFDerivAt f (f' x) x) (hdd : ∀ x, HasFDerivAt f' (f'' x) x)
    {C D E : ℝ} (hb : ∀ x, ‖f x‖ ≤ C) (hdb : ∀ x, ‖f' x‖ ≤ D)
    (hddb : ∀ x, ‖f'' x‖ ≤ E) (x : V) :
    LipschitzWith (Real.toNNReal ((n + 1) * E)) (fun t => heatAverage t f x) := by
  have hE : 0 ≤ E := (norm_nonneg (f'' 0)).trans (hddb 0)
  have hK : 0 ≤ (n + 1 : ℝ) * E := by positivity
  let tr (y : V) := ∑ i : Fin (n + 1), f'' y (EuclideanSpace.single i (1 : ℝ))
    (EuclideanSpace.single i (1 : ℝ))
  have htr : Continuous tr := by dsimp [tr]; fun_prop
  have htrb (y : V) : ‖tr y‖ ≤ (n + 1) * E :=
    (euclidean_hessian_trace_norm_le (f'' y)).trans
      (mul_le_mul_of_nonneg_left (hddb y) (by positivity))
  have hderiv (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) :
      HasDerivAt (fun s => heatAverage s f x) (heatAverage t tr x) t :=
    heatAverage_hasDerivAt_trace hf hf' hf'' hd hdd hb hdb hddb ht x
  have hpos : LipschitzOnWith (Real.toNNReal ((n + 1) * E))
      (fun t => heatAverage t f x) (Ioi (0 : ℝ)) := by
    apply (convex_Ioi (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht => (hderiv t ht).hasDerivWithinAt)
    intro t ht
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hK]
    exact heatAverage_norm_le htr htrb t x
  have hnonneg : LipschitzOnWith (Real.toNNReal ((n + 1) * E))
      (fun t => heatAverage t f x) (Ici (0 : ℝ)) := by
    simpa only [closure_Ioi] using
      LipschitzOnWith.closure (heatAverage_time_continuous hf hb x).continuousOn hpos
  have heq (t : ℝ) : heatAverage t f x = heatAverage (max t 0) f x := by
    by_cases ht : 0 ≤ t
    · rw [max_eq_left ht]
    · have ht' : t ≤ 0 := le_of_not_ge ht
      simp only [heatAverage, max_eq_right ht',
        Real.sqrt_eq_zero_of_nonpos (by linarith : 2 * t ≤ 0), mul_zero, Real.sqrt_zero]
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro s t
  rw [heq s, heq t]
  apply (hnonneg.dist_le_mul (max s 0) (le_max_right s 0) (max t 0) (le_max_right t 0)).trans
  apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg _)
  simpa only [NNReal.coe_one, one_mul, id_eq] using (LipschitzWith.id.max_const 0).dist_le_mul s t

end PoincareConjecture.M35.RadialGauge
