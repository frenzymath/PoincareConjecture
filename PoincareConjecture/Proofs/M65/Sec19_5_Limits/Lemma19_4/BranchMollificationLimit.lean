import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchMollification
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.L2Coefficients
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture.M65Branch

variable {E : Type*} [NormedAddCommGroup E]




theorem memLp_of_bound_support {h : ℂ → E} {R B : ℝ}
    (hh : AEStronglyMeasurable h volume)
    (hs : Function.support h ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ z, ‖h z‖ ≤ B) (p : ℝ≥0∞) : MemLp h p volume := by
  let : IsFiniteMeasure (volume.restrict (closedBall (0 : ℂ) R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : ℂ) R).measure_lt_top.ne
  have hk : MemLp h p (volume.restrict (closedBall (0 : ℂ) R)) :=
    MemLp.of_bound hh.restrict B (ae_of_all _ hb)
  have heq : (closedBall (0 : ℂ) R).indicator h = h :=
    indicator_eq_self.mpr hs
  rw [← heq]
  exact (memLp_indicator_iff_restrict measurableSet_closedBall).mpr hk




theorem integral_norm_sub_pow_tendsto_of_ae
    {f : ℕ → ℂ → E} {g : ℂ → E} {R B : ℝ}
    (hf : ∀ n, AEStronglyMeasurable (f n) volume)
    (hg : AEStronglyMeasurable g volume)
    (hfs : ∀ n, Function.support (f n) ⊆ closedBall (0 : ℂ) R)
    (hgs : Function.support g ⊆ closedBall (0 : ℂ) R)
    (hfb : ∀ n z, ‖f n z‖ ≤ B) (hgb : ∀ z, ‖g z‖ ≤ B)
    (hconv : ∀ᵐ z ∂volume, Tendsto (fun n => f n z) atTop (𝓝 (g z)))
    (p : ℕ) (hp : p ≠ 0) :
    Tendsto (fun n => ∫ z : ℂ, ‖f n z - g z‖ ^ p) atTop (𝓝 0) := by
  let bound : ℂ → ℝ := (closedBall (0 : ℂ) R).indicator (fun _ => (2 * B) ^ p)
  have hi : Integrable bound := by
    apply (integrable_indicator_iff measurableSet_closedBall).mpr
    exact integrableOn_const (isCompact_closedBall (0 : ℂ) R).measure_lt_top.ne
  have hdom (n : ℕ) : ∀ᵐ z ∂volume, ‖‖f n z - g z‖ ^ p‖ ≤ bound z := by
    filter_upwards with z
    by_cases hz : z ∈ closedBall (0 : ℂ) R
    · dsimp only [bound]
      rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _), indicator_of_mem hz]
      have hnorm : ‖f n z - g z‖ ≤ 2 * B :=
        (norm_sub_le _ _).trans ((add_le_add (hfb n z) (hgb z)).trans_eq (by ring))
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm p
    · have hf0 : f n z = 0 := Function.notMem_support.mp (fun h => hz (hfs n h))
      have hg0 : g z = 0 := Function.notMem_support.mp (fun h => hz (hgs h))
      simp only [bound, indicator_of_notMem hz, hf0, hg0, sub_self,
        norm_zero, zero_pow hp, le_refl]
  have hlim : ∀ᵐ z ∂volume, Tendsto (fun n => ‖f n z - g z‖ ^ p) atTop (𝓝 0) := by
    filter_upwards [hconv] with z hz
    simpa only [sub_self, norm_zero, zero_pow hp] using
      (hz.sub (tendsto_const_nhds (x := g z))).norm.pow p
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
    (F := fun n z => ‖f n z - g z‖ ^ p) (f := fun _ => (0 : ℝ)) bound
    (fun n => ((hf n).sub hg).norm.pow p) hi hdom hlim

variable [InnerProductSpace ℝ E]




theorem tendsto_toLp_two_of_bound_support
    {f : ℕ → ℂ → E} {g : ℂ → E} {R B : ℝ}
    (hf : ∀ n, MemLp (f n) 2 volume) (hg : MemLp g 2 volume)
    (hfs : ∀ n, Function.support (f n) ⊆ closedBall (0 : ℂ) R)
    (hgs : Function.support g ⊆ closedBall (0 : ℂ) R)
    (hfb : ∀ n z, ‖f n z‖ ≤ B) (hgb : ∀ z, ‖g z‖ ≤ B)
    (hconv : ∀ᵐ z ∂volume, Tendsto (fun n => f n z) atTop (𝓝 (g z))) :
    Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hg.toLp g)) := by
  have hint := integral_norm_sub_pow_tendsto_of_ae (fun n => (hf n).1) hg.1
    hfs hgs hfb hgb hconv 2 (by norm_num)
  have heq (n : ℕ) : ‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2 =
      ∫ z : ℂ, ‖f n z - g z‖ ^ 2 := by
    rw [Lp.norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hf n).toLp (f n)) (hg.toLp g),
      (hf n).coeFn_toLp, hg.coeFn_toLp] with z hz hfn hgn
    rw [hz, Pi.sub_apply, hfn, hgn]
  have hsq : Tendsto (fun n => ‖(hf n).toLp (f n) - hg.toLp g‖ ^ 2) atTop (𝓝 0) := by
    simpa only [heq] using hint
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsq.sqrt

end PoincareConjecture.M65Branch
