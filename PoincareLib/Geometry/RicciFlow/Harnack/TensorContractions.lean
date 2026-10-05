import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Contractions of Hamilton's Harnack tensors

Finite orthonormal-frame algebra for the trace in Chow et al., *The Ricci
Flow: Techniques and Applications*, Part II, Corollary 15.3, equation (15.18)
(PDF pages 290-291), and Kleiner-Lott, Appendix F, pp. 2850-2851.
Curvature uses the latter's slot convention, with Ricci given by
`Ric k l = ∑ i, Rm k i l i`, as in the frozen metric definitions.
The derivative array below represents covariant Ricci
derivatives; its contraction hypotheses are the two contracted Bianchi
identities. Geometric realization of those identities is a separate step.
-/

open scoped BigOperators

namespace Poincare.RicciFlow.Harnack

variable {I : Type*}

/-- The antisymmetrized covariant derivative of a symmetric two-tensor is
skew in its first two indices. -/
lemma ricciDerivative_skew (A : I → I → I → ℝ) (i j k : I) :
    A i j k - A j i k = -(A j i k - A i j k) := by
  ring

/-- Symmetry of the last two slots gives the cyclic identity for Hamilton's
three-tensor, defined by equation (15.5). -/
lemma ricciDerivative_cyclic (A : I → I → I → ℝ)
    (hA : ∀ i j k, A i j k = A i k j) (i j k : I) :
    (A i j k - A j i k) + (A j k i - A k j i) +
      (A k i j - A i k j) = 0 := by
  rw [hA j i k, hA k j i, hA i k j]
  ring

variable [Fintype I]

/-- Tracing Hamilton's three-tensor gives minus one half of the scalar
gradient, once the contracted Bianchi identities have been supplied. -/
lemma ricciDerivative_trace (A : I → I → I → ℝ) (dR : I → ℝ)
    (hdiv : ∀ i, ∑ p, A p i p = dR i / 2)
    (htrace : ∀ i, ∑ p, A i p p = dR i) (i : I) :
    ∑ p, (A p i p - A i p p) = -(dR i / 2) := by
  rw [Finset.sum_sub_distrib, hdiv, htrace]
  ring

/-- The mixed term in the trace of the Harnack quadratic is the negative
scalar-gradient pairing. -/
lemma ricciDerivative_trace_pairing (A : I → I → I → ℝ) (dR V : I → ℝ)
    (hdiv : ∀ i, ∑ p, A p i p = dR i / 2)
    (htrace : ∀ i, ∑ p, A i p p = dR i) :
    2 * (∑ i, (∑ p, (A p i p - A i p p)) * V i) =
      -(∑ i, dR i * V i) := by
  simp_rw [ricciDerivative_trace A dR hdiv htrace]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The curvature-Ricci term in Hamilton's two-tensor contracts to the
squared Ricci norm. -/
lemma curvatureRicci_trace (Rm : I → I → I → I → ℝ) (Ric : I → I → ℝ)
    (hRic : ∀ k l, ∑ i, Rm k i l i = Ric k l) :
    (∑ i, ∑ k, ∑ l, Rm k i l i * Ric k l) =
      ∑ k, ∑ l, (Ric k l) ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.sum_mul, hRic, pow_two]

/-- Symmetry identifies the trace of the square of Ricci with its squared
norm in an orthonormal frame. -/
lemma ricciSquare_trace (Ric : I → I → ℝ)
    (hsymm : ∀ i k, Ric i k = Ric k i) :
    (∑ i, ∑ k, Ric i k * Ric k i) = ∑ i, ∑ k, (Ric i k) ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [← hsymm i k, pow_two]

/-- The two algebraic reaction terms in Hamilton's two-tensor have trace
equal to the squared Ricci norm. -/
lemma harnackReaction_trace (Rm : I → I → I → I → ℝ) (Ric : I → I → ℝ)
    (hRic : ∀ k l, ∑ i, Rm k i l i = Ric k l)
    (hsymm : ∀ i k, Ric i k = Ric k i) :
    (∑ i, (2 * (∑ k, ∑ l, Rm k i l i * Ric k l) -
      ∑ k, Ric i k * Ric k i)) = ∑ i, ∑ k, (Ric i k) ^ 2 := by
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
    curvatureRicci_trace Rm Ric hRic, ricciSquare_trace Ric hsymm]
  ring

/-- The trace of Hamilton's two-tensor, equation (15.9), in a frame in
which the Laplacian and Hessian contractions are known. -/
lemma harnackTwoTensor_trace (Rm : I → I → I → I → ℝ)
    (Ric LapRic HessR : I → I → ℝ) (lapR τ : ℝ)
    (hRic : ∀ k l, ∑ i, Rm k i l i = Ric k l)
    (hsymm : ∀ i k, Ric i k = Ric k i)
    (hLap : ∑ i, LapRic i i = lapR) (hHess : ∑ i, HessR i i = lapR) :
    (∑ i, (LapRic i i - HessR i i / 2 +
      (2 * (∑ k, ∑ l, Rm k i l i * Ric k l) -
        ∑ k, Ric i k * Ric k i) + Ric i i / (2 * τ))) =
      lapR / 2 + (∑ i, ∑ k, (Ric i k) ^ 2) + (∑ i, Ric i i) / (2 * τ) := by
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]
  rw [hLap, hHess, ← Finset.mul_sum, curvatureRicci_trace Rm Ric hRic,
    ricciSquare_trace Ric hsymm]
  ring

end Poincare.RicciFlow.Harnack
