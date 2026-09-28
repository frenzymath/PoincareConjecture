import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawSpatialCoefficientJets
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.InteriorFiniteJets









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap LineDeriv ContDiff

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckDomainRegularityNative DeTurckHigherDomainNative
  DeTurckGeneratorRegularityNative

variable {n : ℕ} {ι : Type*} [TopologicalSpace ι]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem contDiffOn_supported_ordered_multiplier {a b : ℝ} (hab : a < b)
    (A : ℝ → 𝓢(V, ℝ))
    (hA : ContDiffOn ℝ ∞ (fun p : ℝ × V => A p.1 p.2) (Icc a b ×ˢ univ))
    {S : Set V} (hS : IsCompact S) (hsupport : ∀ t ∈ Icc a b, tsupport (A t) ⊆ S)
    (w : List (Fin n)) :
    ContDiffOn ℝ ∞ (fun t => schwartzMultiplier (orderedSchwartzDerivative w (A t)))
      (Icc a b) := by
  have hjoint : ∀ v : List (Fin n), ContDiffOn ℝ ∞
      (fun p : ℝ × V => orderedSchwartzDerivative v (A p.1) p.2) (Icc a b ×ˢ univ) := by
    intro v
    induction v with
    | nil => exact hA
    | cons i v ih =>
      simpa only [orderedSchwartzDerivative, SchwartzMap.lineDerivOp_apply_eq_fderiv] using
        (raw_family_spatial_fderiv_contDiffOn
          (f := fun t x => orderedSchwartzDerivative v (A t) x) ih).clm_apply
          (contDiffOn_const (c := EuclideanSpace.single i (1 : ℝ)))
  exact contDiffOn_supported_schwartzMultiplier hab _ (hjoint w) hS
    (fun t ht => (tsupport_orderedSchwartzDerivative_subset w (A t)).trans (hsupport t ht))

theorem continuous_iterated_productJet
    (A : ι → 𝓢(V, ℝ)) (q : ι → List (Fin n) → L2) {m : ℕ}
    (hA : ∀ w, w.length ≤ m →
      Continuous (fun t => schwartzMultiplier (orderedSchwartzDerivative w (A t))))
    (hq : ∀ w, w.length ≤ m → Continuous (fun t => q t w))
    (w : List (Fin n)) (hw : w.length ≤ m) :
    Continuous (fun t => ((JetExpression.term (A t) []).iteratedDerivative w).eval (q t)) := by
  have happend (e : JetExpression n) (u v : List (Fin n)) :
      e.iteratedDerivative (u ++ v) = (e.iteratedDerivative v).iteratedDerivative u := by
    induction u with
    | nil => rfl
    | cons i u ih => simp only [List.cons_append, JetExpression.iteratedDerivative, ih]
  have hadd (e f : JetExpression n) (u : List (Fin n)) :
      (e.add f).iteratedDerivative u =
        (e.iteratedDerivative u).add (f.iteratedDerivative u) := by
    induction u with
    | nil => rfl
    | cons i u ih => simp only [JetExpression.iteratedDerivative, ih, JetExpression.derivative]
  have hgeneral : ∀ u v z : List (Fin n),
      u.length + v.length ≤ m → u.length + z.length ≤ m →
      Continuous (fun t =>
        ((JetExpression.term (orderedSchwartzDerivative z (A t)) v).iteratedDerivative u).eval
          (q t)) := by
    intro u
    induction u using List.reverseRecOn with
    | nil =>
      intro v z hv hz
      exact (hA z (by simpa only [List.length_nil, Nat.zero_add] using hz)).clm_apply
        (hq v (by simpa only [List.length_nil, Nat.zero_add] using hv))
    | append_singleton u i ih =>
      intro v z hv hz
      simp only [happend, JetExpression.iteratedDerivative, JetExpression.derivative,
        hadd, JetExpression.eval]
      exact (ih (i :: v) z (by
          simp only [List.length_append, List.length_cons, List.length_nil] at hv ⊢
          omega) (by
          simp only [List.length_append, List.length_cons, List.length_nil] at hz
          omega)).add (ih v (i :: z) (by
            simp only [List.length_append, List.length_cons, List.length_nil] at hv
            omega) (by
              simp only [List.length_append, List.length_cons, List.length_nil] at hz ⊢
              omega))
  exact hgeneral w [] [] (by simpa only [List.length_nil, Nat.add_zero] using hw)
    (by simpa only [List.length_nil, Nat.add_zero] using hw)

end PoincareConjecture.M35.Uniqueness.Heat
