import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Angular-gap configurations for normalized circle triangulations

Positive cyclic gaps shorter than a semicircle, with total angle two pi and
a prescribed first gap, form a nonempty convex and hence contractible space.
These are the coordinate conditions for the circle-triangulation step in
Cairns 1940, Section 6, p. 802, and Lemma 11.1, p. 807, footnote 14.
See M76 derivation 13. The geometric correspondence with Brouwer-star
transverse-plane spaces is a separate obligation.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M76.Smoothing

/-- Cyclic short-arc gap coordinates for n+3 vertices, with the first two
marked vertices separated by `theta`. See Cairns pp. 802, 807 and
M76 derivation 13. -/
def shortArcGapSpace (n : ℕ) (theta : ℝ) : Set (Fin (n + 3) → ℝ) :=
  {w | (∀ i, w i ∈ Ioo (0 : ℝ) Real.pi) ∧
    (∑ i, w i) = 2 * Real.pi ∧ w 0 = theta}

/-- The angular-gap constraints are convex, so linear interpolation preserves
them. This is the coordinate calculation behind Cairns p. 807, footnote 14;
see M76 derivation 13. -/
theorem convex_shortArcGapSpace (n : ℕ) (theta : ℝ) :
    Convex ℝ (shortArcGapSpace n theta) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, ?_, ?_⟩
  · exact (convex_Ioo (0 : ℝ) Real.pi) (hx.1 i) (hy.1 i) ha hb hab
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hx.2.1, hy.2.1, ← add_mul, hab, one_mul]
  · change a * x 0 + b * y 0 = theta
    rw [hx.2.2, hy.2.2, ← add_mul, hab, one_mul]

/-- Equal gaps on the complementary arc give a configuration for every
admissible first gap. See Cairns p. 807, footnote 14 and M76 derivation 13. -/
theorem nonempty_shortArcGapSpace (n : ℕ) {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) : (shortArcGapSpace n theta).Nonempty := by
  let r : ℝ := (2 * Real.pi - theta) / (n + 2)
  have hn : (0 : ℝ) < n + 2 := by positivity
  have hr0 : 0 < r := div_pos (by linarith [Real.pi_pos, htheta.2]) hn
  have hrpi : r < Real.pi := by
    rw [div_lt_iff₀ hn]
    nlinarith [htheta.1, mul_nonneg Real.pi_pos.le (Nat.cast_nonneg (α := ℝ) n)]
  refine ⟨Fin.cons theta (fun _ : Fin (n + 2) => r), ?_, ?_, by simp⟩
  · intro i
    exact Fin.cases htheta (fun _ => ⟨hr0, hrpi⟩) i
  · simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat]
    dsimp only [r]
    field_simp [ne_of_gt hn]
    ring

/-- The normalized short-arc coordinate space is contractible. The geometric
identification with Cairns' T(r^1) is separate; see p. 807, footnote 14 and
M76 derivation 13. -/
theorem contractible_shortArcGapSpace (n : ℕ) {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi) :
    ContractibleSpace (shortArcGapSpace n theta) :=
  (convex_shortArcGapSpace n theta).contractibleSpace (nonempty_shortArcGapSpace n htheta)

end PoincareMT.M76.Smoothing
