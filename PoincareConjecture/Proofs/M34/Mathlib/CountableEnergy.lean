import PoincareConjecture.Proofs.M03.ScalarEnergyComparison
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Topology.Algebra.InfiniteSum.Order

set_option autoImplicit false

open Set

theorem eq_zero_of_summable_weighted_energy_rates
    {ι : Type*} {E : ι → ℝ → ℝ} {w u v : ι → ℝ} {a b C : ℝ}
    (hw : ∀ i, 0 < w i) (hu : Summable u) (hv : Summable v)
    (hc : ∀ i, ContinuousOn (E i) (Icc a b))
    (hd : ∀ i t, t ∈ Ioo a b → DifferentiableAt ℝ (E i) t)
    (hb : ∀ i t, t ∈ Icc a b → ‖w i * E i t‖ ≤ u i)
    (hbd : ∀ i t, t ∈ Ioo a b → ‖w i * deriv (E i) t‖ ≤ v i)
    (hzero : ∀ i, E i a = 0)
    (hn : ∀ i t, t ∈ Icc a b → 0 ≤ E i t)
    (hr : ∀ t ∈ Ioo a b,
      (∑' i, w i * deriv (E i) t) ≤ C * (∑' i, w i * E i t)) :
    ∀ i, EqOn (E i) (fun _ => 0) (Icc a b) := by
  let total : ℝ → ℝ := fun t => ∑' i, w i * E i t
  have hs (t : ℝ) (ht : t ∈ Icc a b) :
      Summable (fun i => w i * E i t) :=
    Summable.of_norm_bounded hu (fun i => hb i t ht)
  have hct : ContinuousOn total (Icc a b) :=
    continuousOn_tsum (fun i => continuousOn_const.mul (hc i)) hu hb
  have hdt (t : ℝ) (ht : t ∈ Ioo a b) :
      HasDerivAt total (∑' i, w i * deriv (E i) t) t :=
    hasDerivAt_tsum_of_isPreconnected hv isOpen_Ioo (convex_Ioo a b).isPreconnected
      (fun i s hs => (hd i s hs).hasDerivAt.const_mul (w i)) hbd ht
      (hs t ⟨ht.1.le, ht.2.le⟩) ht
  have htz : total a = 0 := by simp only [total, hzero, mul_zero, tsum_zero]
  have htn (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ total t :=
    tsum_nonneg (fun i => mul_nonneg (hw i).le (hn i t ht))
  have htzero : EqOn total (fun _ => 0) (Icc a b) :=
    PoincareConjecture.Proofs.M03.eq_zero_on_interval_of_deriv_le_mul hct
      (fun t ht => (hdt t ht).differentiableAt) htz htn (fun t ht => by
        rw [(hdt t ht).deriv]
        exact hr t ht)
  intro i t ht
  have hle : w i * E i t ≤ total t :=
    (hs t ht).le_tsum i (fun j _ => mul_nonneg (hw j).le (hn j t ht))
  rw [htzero ht] at hle
  exact le_antisymm (by nlinarith [hw i]) (hn i t ht)
