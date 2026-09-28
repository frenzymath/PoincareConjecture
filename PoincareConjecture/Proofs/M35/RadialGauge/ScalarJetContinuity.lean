import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Deriv










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff BigOperators

namespace PoincareConjecture.M35.RadialGauge

variable {A : Type*} [TopologicalSpace A]


theorem scalar_jet_continuous_sub {f g : A → ℝ → ℝ} (n : ℕ)
    (hf : ∀ a, ContDiff ℝ ∞ (f a)) (hg : ∀ a, ContDiff ℝ ∞ (g a))
    (hfc : Continuous (fun p : A × ℝ => iteratedDeriv n (f p.1) p.2))
    (hgc : Continuous (fun p : A × ℝ => iteratedDeriv n (g p.1) p.2)) :
    Continuous (fun p : A × ℝ => iteratedDeriv n (fun r => f p.1 r - g p.1 r) p.2) := by
  have heq (p : A × ℝ) := iteratedDeriv_fun_sub (x := p.2)
    (((hf p.1).contDiffAt).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n))
    (((hg p.1).contDiffAt).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n))
  simpa only [heq, Function.comp_def] using continuous_sub.comp (hfc.prodMk hgc)



theorem scalar_jet_continuous_mul {f g : A → ℝ → ℝ} (n : ℕ)
    (hf : ∀ a, ContDiff ℝ ∞ (f a)) (hg : ∀ a, ContDiff ℝ ∞ (g a))
    (hfc : ∀ j ≤ n, Continuous (fun p : A × ℝ => iteratedDeriv j (f p.1) p.2))
    (hgc : ∀ j ≤ n, Continuous (fun p : A × ℝ => iteratedDeriv j (g p.1) p.2)) :
    Continuous (fun p : A × ℝ => iteratedDeriv n (fun r => f p.1 r * g p.1 r) p.2) := by
  have heq (p : A × ℝ) := iteratedDeriv_fun_mul (x := p.2)
    (((hf p.1).contDiffAt).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n))
    (((hg p.1).contDiffAt).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n))
  simp_rw [heq]
  apply continuous_finsetSum
  intro i hi
  exact (continuous_const.mul (hfc i (by simpa only
    [Finset.mem_range, Nat.lt_succ_iff] using hi))).mul (hgc (n - i) (Nat.sub_le _ _))



theorem scalar_jets_continuous_inv {f : A → ℝ → ℝ}
    (hf : ∀ a, ContDiff ℝ ∞ (f a)) (hne : ∀ a r, f a r ≠ 0)
    (hfc : ∀ j : ℕ, Continuous (fun p : A × ℝ => iteratedDeriv j (f p.1) p.2)) :
    ∀ j : ℕ, Continuous (fun p : A × ℝ =>
      iteratedDeriv j (fun r => (f p.1 r)⁻¹) p.2) := by
  let q (a : A) (r : ℝ) := (f a r)⁻¹
  have hq (a : A) : ContDiff ℝ ∞ (q a) := (hf a).inv (hne a)
  have hd (a : A) : deriv (q a) =
      fun r => (-deriv (f a) r) * (q a r * q a r) := by
    funext r
    have hh := (((hf a).differentiable (by simp) r).hasDerivAt.fun_inv (hne a r)).deriv
    simpa only [q, Pi.inv_apply, div_eq_mul_inv, pow_two, mul_inv_rev,
      neg_mul, mul_assoc] using hh
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      cases j with
      | zero =>
          simpa only [iteratedDeriv_zero, Pi.inv_apply] using
            (hfc 0).fun_inv₀ (fun p => hne p.1 p.2)
      | succ n =>
          have hqc (i : ℕ) (hi : i ≤ n) :
              Continuous (fun p : A × ℝ => iteratedDeriv i (q p.1) p.2) :=
            ih i (Nat.lt_succ_of_le hi)
          have hsq (i : ℕ) (hi : i ≤ n) : Continuous (fun p : A × ℝ =>
              iteratedDeriv i (fun r => q p.1 r * q p.1 r) p.2) :=
            scalar_jet_continuous_mul i hq hq
              (fun j hj => hqc j (hj.trans hi)) (fun j hj => hqc j (hj.trans hi))
          have hneg (i : ℕ) : Continuous (fun p : A × ℝ =>
              iteratedDeriv i (fun r => -deriv (f p.1) r) p.2) := by
            simpa only [iteratedDeriv_fun_neg, ← iteratedDeriv_succ', Function.comp_def]
              using continuous_neg.comp (hfc (i + 1))
          have hm := scalar_jet_continuous_mul n
            (fun a => (contDiff_infty_iff_deriv.mp (hf a)).2.neg)
            (fun a => (hq a).mul (hq a)) (fun i _ => hneg i) hsq
          change Continuous (fun p : A × ℝ => iteratedDeriv (n + 1) (q p.1) p.2)
          simpa only [iteratedDeriv_succ', hd] using hm



theorem scalar_jets_continuous_log {f : A → ℝ → ℝ}
    (hf : ∀ a, ContDiff ℝ ∞ (f a)) (hne : ∀ a r, f a r ≠ 0)
    (hfc : ∀ j : ℕ, Continuous (fun p : A × ℝ => iteratedDeriv j (f p.1) p.2)) :
    ∀ j : ℕ, Continuous (fun p : A × ℝ =>
      iteratedDeriv j (fun r => Real.log (f p.1 r)) p.2) := by
  have hi := scalar_jets_continuous_inv hf hne hfc
  have hd (a : A) : deriv (fun r => Real.log (f a r)) =
      fun r => deriv (f a) r * (f a r)⁻¹ := by
    funext r
    simpa only [div_eq_mul_inv] using
      (((hf a).differentiable (by simp) r).hasDerivAt.log (hne a r)).deriv
  intro j
  cases j with
  | zero =>
      simpa only [iteratedDeriv_zero] using (hfc 0).log (fun p => hne p.1 p.2)
  | succ n =>
      have hdf (i : ℕ) : Continuous (fun p : A × ℝ =>
          iteratedDeriv i (deriv (f p.1)) p.2) := by
        simpa only [iteratedDeriv_succ'] using hfc (i + 1)
      have hm := scalar_jet_continuous_mul n
        (fun a => (contDiff_infty_iff_deriv.mp (hf a)).2)
        (fun a => (hf a).inv (hne a)) (fun i _ => hdf i) (fun i _ => hi i)
      simpa only [iteratedDeriv_succ', hd, Pi.inv_apply] using hm



theorem scalar_jets_continuous_exp {f : A → ℝ → ℝ}
    (hf : ∀ a, ContDiff ℝ ∞ (f a))
    (hfc : ∀ j : ℕ, Continuous (fun p : A × ℝ => iteratedDeriv j (f p.1) p.2)) :
    ∀ j : ℕ, Continuous (fun p : A × ℝ =>
      iteratedDeriv j (fun r => Real.exp (f p.1 r)) p.2) := by
  have hd (a : A) : deriv (fun r => Real.exp (f a r)) =
      fun r => Real.exp (f a r) * deriv (f a) r :=
    funext (fun r => (((hf a).differentiable (by simp) r).hasDerivAt.exp).deriv)
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      cases j with
      | zero => simpa only [iteratedDeriv_zero] using (hfc 0).rexp
      | succ n =>
          have hdf (i : ℕ) : Continuous (fun p : A × ℝ =>
              iteratedDeriv i (deriv (f p.1)) p.2) := by
            simpa only [iteratedDeriv_succ'] using hfc (i + 1)
          have hm := scalar_jet_continuous_mul n (fun a => (hf a).exp)
            (fun a => (contDiff_infty_iff_deriv.mp (hf a)).2)
            (fun i hi => ih i (Nat.lt_succ_of_le hi)) (fun i _ => hdf i)
          simpa only [iteratedDeriv_succ', hd] using hm

end PoincareConjecture.M35.RadialGauge
