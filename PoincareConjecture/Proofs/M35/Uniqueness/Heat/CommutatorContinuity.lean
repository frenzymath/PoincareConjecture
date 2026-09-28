import PoincareConjecture.Proofs.M35.Uniqueness.Heat.JetFamilyContinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap LineDeriv

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative
  DeTurckDomainRegularityNative

variable {n : ℕ} {ι : Type*} [TopologicalSpace ι]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

private theorem iteratedDerivative_append (e : JetExpression n) (u v : List (Fin n)) :
    e.iteratedDerivative (u ++ v) = (e.iteratedDerivative v).iteratedDerivative u := by
  induction u with
  | nil => rfl
  | cons i u ih => simp only [List.cons_append, JetExpression.iteratedDerivative, ih]

private theorem iteratedDerivative_add (e f : JetExpression n) (u : List (Fin n)) :
    (e.add f).iteratedDerivative u =
      (e.iteratedDerivative u).add (f.iteratedDerivative u) := by
  induction u with
  | nil => rfl
  | cons i u ih => simp only [JetExpression.iteratedDerivative, ih, JetExpression.derivative]

private theorem iteratedDerivative_sum (e : Fin n → JetExpression n) (u : List (Fin n)) :
    (JetExpression.sum e).iteratedDerivative u =
      .sum (fun i => (e i).iteratedDerivative u) := by
  induction u with
  | nil => rfl
  | cons i u ih => simp only [JetExpression.iteratedDerivative, ih, JetExpression.derivative]

theorem continuous_iterated_termJet (A : ι → 𝓢(V, ℝ))
    (q : ι → List (Fin n) → L2) {m : ℕ}
    (hA : ∀ w, w.length ≤ m →
      Continuous (fun t => schwartzMultiplier (orderedSchwartzDerivative w (A t))))
    (hq : ∀ w, w.length ≤ m → Continuous (fun t => q t w))
    (u v z : List (Fin n)) (hv : u.length + v.length ≤ m) (hz : u.length + z.length ≤ m) :
    Continuous (fun t =>
      ((JetExpression.term (orderedSchwartzDerivative z (A t)) v).iteratedDerivative u).eval
        (q t)) := by
  revert v z
  induction u using List.reverseRecOn with
  | nil =>
    intro v z hv hz
    exact (hA z (by simpa only [List.length_nil, Nat.zero_add] using hz)).clm_apply
      (hq v (by simpa only [List.length_nil, Nat.zero_add] using hv))
  | append_singleton u i ih =>
    intro v z hv hz
    simp only [iteratedDerivative_append, JetExpression.iteratedDerivative,
      JetExpression.derivative, iteratedDerivative_add, JetExpression.eval]
    exact (ih (i :: v) z (by
        simp only [List.length_append, List.length_cons, List.length_nil] at hv ⊢
        omega) (by
        simp only [List.length_append, List.length_cons, List.length_nil] at hz
        omega)).add (ih v (i :: z) (by
          simp only [List.length_append, List.length_cons, List.length_nil] at hv
          omega) (by
            simp only [List.length_append, List.length_cons, List.length_nil] at hz ⊢
            omega))

theorem continuous_commutatorExpression
    (A : ι → Fin n → Fin n → 𝓢(V, ℝ)) (q : ι → List (Fin n) → L2) {m : ℕ}
    (hA : ∀ i j w, w.length ≤ m →
      Continuous (fun t => schwartzMultiplier (orderedSchwartzDerivative w (A t i j))))
    (hq : ∀ w, w.length ≤ m → Continuous (fun t => q t w))
    (w : List (Fin n)) (hw : w.length + 1 ≤ m) :
    Continuous (fun t => (commutatorExpression (A t) w).eval (q t)) := by
  have hgeneral : ∀ v u : List (Fin n), v.length + u.length + 1 ≤ m →
      Continuous (fun t => ((commutatorExpression (A t) v).iteratedDerivative u).eval (q t)) := by
    intro v
    induction v with
    | nil =>
      intro u _hu
      have hz : ∀ z : List (Fin n), (JetExpression.zero (n := n)).iteratedDerivative z = .zero := by
        intro z
        induction z with
        | nil => rfl
        | cons i z ih => simp only [JetExpression.iteratedDerivative, ih, JetExpression.derivative]
      simpa only [commutatorExpression, hz, JetExpression.eval] using
        (continuous_const : Continuous (fun _ : ι => (0 : L2)))
    | cons k v ih =>
      intro u hu
      have hleft : Continuous (fun t =>
          (((commutatorExpression (A t) v).derivative k).iteratedDerivative u).eval (q t)) := by
        simpa only [iteratedDerivative_append, JetExpression.iteratedDerivative] using
          ih (u ++ [k]) (by
            simp only [List.length_append, List.length_singleton]
            simp only [List.length_cons] at hu
            omega)
      simp only [commutatorExpression, iteratedDerivative_add, iteratedDerivative_sum,
        JetExpression.eval]
      refine hleft.add (continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ => ?_)))
      have h₁ := continuous_iterated_termJet (fun t => A t i j) q (hA i j) hq
        u (i :: v) [j, k] (by simp only [List.length_cons] at hu ⊢; omega)
        (by simp only [List.length_cons, List.length_nil] at hu ⊢; omega)
      have h₂ := continuous_iterated_termJet (fun t => A t i j) q (hA i j) hq
        u (j :: i :: v) [k] (by simp only [List.length_cons] at hu ⊢; omega)
        (by simp only [List.length_cons, List.length_nil] at hu ⊢; omega)
      simpa only [orderedSchwartzDerivative, Pi.add_def] using! h₁.add h₂
  simpa only [List.length_nil, Nat.add_zero, JetExpression.iteratedDerivative] using
    hgeneral w [] hw

theorem continuous_commutedSource
    (A : ι → Fin n → Fin n → 𝓢(V, ℝ)) (g q : ι → List (Fin n) → L2) {s : ℕ}
    (hA : ∀ i j w, w.length ≤ s + 1 →
      Continuous (fun t => schwartzMultiplier (orderedSchwartzDerivative w (A t i j))))
    (hq : ∀ w, w.length ≤ s + 1 → Continuous (fun t => q t w))
    (hg : ∀ w, w.length ≤ s → Continuous (fun t => g t w))
    (w : List (Fin n)) (hw : w.length ≤ s) :
    Continuous (fun t => commutedSource (A t) (g t) (q t) w) :=
  (hg w hw).add (continuous_commutatorExpression A q hA hq w (by omega))

end PoincareConjecture.M35.Uniqueness.Heat
