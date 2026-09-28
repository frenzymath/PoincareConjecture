import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FiniteJetEllipticBound










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

def jetExpressionBound : JetExpression n → ℝ
  | .zero => 0
  | .term a _ => ‖schwartzMultiplier a‖
  | .add e f => jetExpressionBound e + jetExpressionBound f
  | .sum f => ∑ i, jetExpressionBound (f i)

theorem jetExpressionBound_nonneg (e : JetExpression n) : 0 ≤ jetExpressionBound e := by
  induction e with
  | zero => exact le_rfl
  | term a w => exact norm_nonneg _
  | add e f he hf => exact add_nonneg he hf
  | sum f hf => exact Finset.sum_nonneg (fun i _ => hf i)

theorem norm_jetExpression_eval_le (e : JetExpression n) {s : ℕ}
    (he : e.orderLE s) (q : List (Fin n) → L2) {M : ℝ}
    (hq : ∀ w, w.length ≤ s → ‖q w‖ ≤ M) :
    ‖e.eval q‖ ≤ jetExpressionBound e * M := by
  induction e with
  | zero => simp only [JetExpression.eval, jetExpressionBound, norm_zero, zero_mul, le_refl]
  | term a w =>
    exact ((schwartzMultiplier a).le_opNorm (q w)).trans
      (mul_le_mul_of_nonneg_left (hq w he) (norm_nonneg _))
  | add e f ihe ihf =>
    exact (norm_add_le _ _).trans (by
      simpa only [jetExpressionBound, add_mul] using add_le_add (ihe he.1) (ihf he.2))
  | sum f ih =>
    exact (norm_sum_le _ _).trans (by
      simpa only [jetExpressionBound, Finset.sum_mul] using
        Finset.sum_le_sum (fun i _ => ih i (he i)))

theorem norm_commutedSource_le
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (g q : List (Fin n) → L2)
    (w : List (Fin n)) {M : ℝ}
    (hq : ∀ v, v.length ≤ w.length + 1 → ‖q v‖ ≤ M) :
    ‖commutedSource A g q w‖ ≤
      ‖g w‖ + jetExpressionBound (commutatorExpression A w) * M :=
  (norm_add_le _ _).trans (add_le_add le_rfl
    (norm_jetExpression_eval_le _ (commutatorExpression_order A w) q hq))

theorem norm_weakJet_commuted_second_le_bounds (q g : List (Fin n) → L2) {s : ℕ}
    (hq : IsWeakSchwartzJet q (s + 2)) (hg : IsWeakSchwartzJet g s)
    {K : Set V} (hK : IsCompact K) (hqK : ∀ᵐ x ∂volume, x ∉ K → q [] x = 0)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) {r ell B M N : ℝ}
    (hr : 0 < r) (hell : 0 < ell) (hB : 0 ≤ B)
    (hEll : ∀ x ∈ Metric.cthickening (3 * r) K, ∀ ξ : Fin n → ℝ,
      ell * (∑ i, ξ i ^ 2) ≤ ∑ i, ∑ j, A i j x * ξ i * ξ j)
    (hAB : ∀ i j x, ‖fderiv ℝ (A i j) x‖ ≤ B)
    (heq : DivergenceEquation A (fun i => q [i]) (g []) (Metric.cthickening (3 * r) K))
    (w : List (Fin n)) (hw : w.length ≤ s)
    (hqM : ∀ v, v.length ≤ w.length + 1 → ‖q v‖ ≤ M)
    (hgN : ‖g w‖ ≤ N) (i j : Fin n) :
    ‖q (j :: i :: w)‖ ≤
      (N + jetExpressionBound (commutatorExpression A w) * M + (n : ℝ) ^ 2 * B * M) / ell := by
  have hsum : (∑ l, ‖q (l :: w)‖) ≤ (n : ℝ) * M := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      using Finset.sum_le_sum (fun l (_hl : l ∈ (Finset.univ : Finset (Fin n))) =>
        hqM (l :: w) (by simp only [List.length_cons, le_refl]))
  have hsource := (norm_commutedSource_le A g q w hqM).trans
    (add_le_add hgN le_rfl)
  refine (norm_weakJet_commuted_second_le q g hq hg hK hqK A hr hell hB hEll hAB
    heq w hw i j).trans (div_le_div_of_nonneg_right ?_ hell.le)
  have hfirst := add_le_add hsource
    (mul_le_mul_of_nonneg_left hsum (mul_nonneg (Nat.cast_nonneg n) hB))
  convert hfirst using 1
  ring

end PoincareConjecture.M35.Uniqueness.Heat
