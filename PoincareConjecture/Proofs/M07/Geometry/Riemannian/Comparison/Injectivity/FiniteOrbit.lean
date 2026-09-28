import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Lifting.SmoothDeck
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Convex.Deriv

noncomputable section
set_option autoImplicit false

open Set Function

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_finite_orbit_energy_center
    {m : ℕ} (hm : 0 < m) {r δ : ℝ} (hr : 0 ≤ r)
    (A : Fin m → E → E)
    (hA : ∀ i, ContinuousOn (A i) (Metric.closedBall 0 r))
    (hA0 : ∀ z ∈ Metric.closedBall 0 r, A ⟨0, hm⟩ z = z)
    (hcenter : ∀ i, ‖A i 0‖ ≤ δ) :
    ∃ y ∈ Metric.closedBall (0 : E) r,
      IsMinOn (fun z => ∑ i, ‖A i z‖ ^ 2) (Metric.closedBall 0 r) y ∧
      ‖y‖ ^ 2 ≤ (m : ℝ) * δ ^ 2 := by
  classical
  have hzero : (0 : E) ∈ Metric.closedBall 0 r := by simpa using hr
  have hcont : ContinuousOn (fun z => ∑ i, ‖A i z‖ ^ 2)
      (Metric.closedBall 0 r) := continuousOn_finsetSum _ (fun i _ => (hA i).norm.pow 2)
  obtain ⟨y, hy, hmin⟩ := (isCompact_closedBall (0 : E) r).exists_isMinOn ⟨0, hzero⟩ hcont
  refine ⟨y, hy, hmin, ?_⟩
  have hterm : ‖y‖ ^ 2 ≤ ∑ i, ‖A i y‖ ^ 2 := by
    calc
      ‖y‖ ^ 2 = ‖A ⟨0, hm⟩ y‖ ^ 2 := by rw [hA0 y hy]
      _ ≤ ∑ i, ‖A i y‖ ^ 2 :=
        Finset.single_le_sum (fun i _ => sq_nonneg (‖A i y‖))
          (Finset.mem_univ (⟨0, hm⟩ : Fin m))
  have hsum : (∑ i, ‖A i 0‖ ^ 2) ≤ (m : ℝ) * δ ^ 2 := by
    calc
      (∑ i, ‖A i 0‖ ^ 2) ≤ ∑ _i : Fin m, δ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ (norm_nonneg _) (hcenter i) 2
      _ = (m : ℝ) * δ ^ 2 := by simp
  exact hterm.trans ((hmin hzero).trans hsum)

theorem eq_of_strictConvexOn_curve_of_isMinOn
    {X : Type*} {K : Set X} {F : X → ℝ} {x y : X}
    (hx : IsMinOn F K x) (hy : IsMinOn F K y)
    (c : ℝ → X) (hc : MapsTo c (Icc (0 : ℝ) 1) K)
    (hc0 : c 0 = x) (hc1 : c 1 = y)
    (hstrict : x ≠ y → StrictConvexOn ℝ (Icc (0 : ℝ) 1) (F ∘ c)) : x = y := by
  by_contra hne
  have hmin0 : IsMinOn (F ∘ c) (Icc (0 : ℝ) 1) 0 := by
    intro t ht
    change F (c 0) ≤ F (c t)
    rw [hc0]
    exact hx (hc ht)
  have hmin1 : IsMinOn (F ∘ c) (Icc (0 : ℝ) 1) 1 := by
    intro t ht
    change F (c 1) ≤ F (c t)
    rw [hc1]
    exact hy (hc ht)
  have h := (hstrict hne).eq_of_isMinOn hmin0 hmin1 (by simp) (by simp)
  norm_num at h

theorem sum_iterate_eq_of_period
    {X : Type*} (d : X → X) (F : X → ℝ) {m : ℕ} {y : X}
    (hperiod : d^[m] y = y) :
    (∑ i : Fin m, F (d^[i.val] (d y))) = ∑ i : Fin m, F (d^[i.val] y) := by
  have htel (k : ℕ) :
      (∑ i : Fin k, F (d^[i.val] (d y))) + F y =
        (∑ i : Fin k, F (d^[i.val] y)) + F (d^[k] y) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [← Function.iterate_succ_apply]
      linarith
  have h := htel m
  rw [hperiod] at h
  linarith

theorem exists_two_finite_orbit_energy_minimizers
    {m : ℕ} (hm : 0 < m) {r δ : ℝ} (hr : 0 < r)
    (hδ : δ < r / 16) (henergy : (m : ℝ) * δ ^ 2 < (r / 16) ^ 2)
    (d : E → E)
    (hcont : ∀ i : Fin m, ContinuousOn (d^[i.val]) (Metric.closedBall 0 r))
    (hcenter : ∀ i : Fin m, ‖d^[i.val] 0‖ ≤ δ)
    (hperiod : EqOn (d^[m]) id (Metric.closedBall 0 r))
    (hdisplace : ∀ x ∈ Metric.closedBall (0 : E) r, ‖d x‖ ≤ δ + 2 * ‖x‖)
    (hfree : ∀ x ∈ Metric.closedBall (0 : E) r, d x ≠ x) :
    ∃ y : E, y ≠ d y ∧ ‖y‖ < r / 16 ∧ ‖d y‖ < 3 * r / 16 ∧
      IsMinOn (fun z => ∑ i : Fin m, ‖d^[i.val] z‖ ^ 2)
        (Metric.closedBall 0 r) y ∧
      IsMinOn (fun z => ∑ i : Fin m, ‖d^[i.val] z‖ ^ 2)
        (Metric.closedBall 0 r) (d y) := by
  obtain ⟨y, hy, hmin, hyenergy⟩ := exists_finite_orbit_energy_center hm hr.le
    (fun i : Fin m => d^[i.val]) hcont (by simp) hcenter
  have hybound : ‖y‖ < r / 16 := by
    have hsquare := hyenergy.trans_lt henergy
    nlinarith [norm_nonneg y]
  have hdybound : ‖d y‖ < 3 * r / 16 := by
    have hd := hdisplace y hy
    linarith
  refine ⟨y, (hfree y hy).symm, hybound, hdybound, hmin, ?_⟩
  intro z hz
  change (∑ i : Fin m, ‖d^[i.val] (d y)‖ ^ 2) ≤ _
  rw [sum_iterate_eq_of_period d (fun z => ‖z‖ ^ 2) (hperiod hy)]
  exact hmin hz

end PoincareConjecture
