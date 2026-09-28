import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Choose.Sum









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffAt_iteratedDeriv_infty {u : ℝ → E} {t : ℝ}
    (hu : ContDiffAt ℝ ∞ u t) (k : ℕ) : ContDiffAt ℝ ∞ (iteratedDeriv k u) t := by
  induction k with
  | zero => exact hu
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ih.derivWithin (by simp)

theorem hasDerivAt_iteratedDeriv_infty {u : ℝ → E} {t : ℝ}
    (hu : ContDiffAt ℝ ∞ u t) (k : ℕ) :
    HasDerivAt (iteratedDeriv k u) (iteratedDeriv (k + 1) u t) t := by
  rw [iteratedDeriv_succ]
  exact ((contDiffAt_iteratedDeriv_infty hu k).differentiableAt (by simp)).hasDerivAt

def timeOperatorJet (A : ℕ → ℝ → E →L[ℝ] F) (u : ℕ → ℝ → E) (k : ℕ) (t : ℝ) : F :=
  ∑ p ∈ Finset.antidiagonal k, k.choose p.1 • A p.1 t (u p.2 t)

theorem timeOperatorJet_zero (A : ℕ → ℝ → E →L[ℝ] F) (u : ℕ → ℝ → E) (t : ℝ) :
    timeOperatorJet A u 0 t = A 0 t (u 0 t) := by
  simp only [timeOperatorJet, Finset.Nat.antidiagonal_zero, Finset.sum_singleton,
    Nat.choose_zero_right, one_smul]

theorem hasDerivAt_timeOperatorJet (A : ℕ → ℝ → E →L[ℝ] F) (u : ℕ → ℝ → E)
    {t : ℝ} (hA : ∀ j, HasDerivAt (A j) (A (j + 1) t) t)
    (hu : ∀ j, HasDerivAt (u j) (u (j + 1) t) t) (k : ℕ) :
    HasDerivAt (timeOperatorJet A u k) (timeOperatorJet A u (k + 1) t) t := by
  have hd := HasDerivAt.fun_sum (u := Finset.antidiagonal k)
    (fun p _ => ((hA p.1).clm_apply (hu p.2)).fun_const_smul (k.choose p.1))
  have he : (∑ p ∈ Finset.antidiagonal k,
      k.choose p.1 • (A (p.1 + 1) t (u p.2 t) + A p.1 t (u (p.2 + 1) t))) =
      timeOperatorJet A u (k + 1) t := by
    rw [timeOperatorJet, Finset.sum_antidiagonal_choose_succ_nsmul
      (fun i j => A i t (u j t)) k]
    simp only [smul_add, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    rw [Nat.choose_symm_of_eq_add (Finset.mem_antidiagonal.mp hp).symm]
  exact he ▸ hd

theorem iteratedDeriv_eq_timeOperatorJet (A : ℕ → ℝ → E →L[ℝ] F) (u : ℕ → ℝ → E)
    {S : Set ℝ} (hS : IsOpen S)
    (hA : ∀ j, ∀ t ∈ S, HasDerivAt (A j) (A (j + 1) t) t)
    (hu : ∀ j, ∀ t ∈ S, HasDerivAt (u j) (u (j + 1) t) t)
    (k : ℕ) {t : ℝ} (ht : t ∈ S) :
    iteratedDeriv k (fun s => A 0 s (u 0 s)) t = timeOperatorJet A u k t := by
  induction k generalizing t with
  | zero => exact (timeOperatorJet_zero A u t).symm
  | succ k ih =>
    have he : iteratedDeriv k (fun s => A 0 s (u 0 s)) =ᶠ[𝓝 t] timeOperatorJet A u k := by
      filter_upwards [hS.mem_nhds ht] with s hs
      exact ih hs
    rw [iteratedDeriv_succ]
    exact he.deriv_eq.trans (hasDerivAt_timeOperatorJet A u
      (fun j => hA j t ht) (fun j => hu j t ht) k).deriv

theorem linearHeat_timeJet_equation (J : E →L[ℝ] F)
    (A : ℕ → ℝ → E →L[ℝ] F) (u : ℕ → ℝ → E)
    {S : Set ℝ} (hS : IsOpen S)
    (hA : ∀ j, ∀ t ∈ S, HasDerivAt (A j) (A (j + 1) t) t)
    (hu : ∀ j, ∀ t ∈ S, HasDerivAt (u j) (u (j + 1) t) t)
    (heq : ∀ t ∈ S, J (u 1 t) = A 0 t (u 0 t))
    (k : ℕ) {t : ℝ} (ht : t ∈ S) : J (u (k + 1) t) = timeOperatorJet A u k t := by
  induction k generalizing t with
  | zero => exact (heq t ht).trans (timeOperatorJet_zero A u t).symm
  | succ k ih =>
    have he : (fun s => J (u (k + 1) s)) =ᶠ[𝓝 t] timeOperatorJet A u k := by
      filter_upwards [hS.mem_nhds ht] with s hs
      exact ih hs
    have hl := J.hasFDerivAt.comp_hasDerivAt t (hu (k + 1) t ht)
    have hr := hasDerivAt_timeOperatorJet A u
      (fun j => hA j t ht) (fun j => hu j t ht) k
    exact hl.deriv.symm.trans (he.deriv_eq.trans hr.deriv)

end PoincareConjecture.M35.Uniqueness.Heat
