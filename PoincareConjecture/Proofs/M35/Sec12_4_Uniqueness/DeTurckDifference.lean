import PoincareConjecture.Proofs.M03.Existence.DeTurckMetricProducerNative










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Matrix.Norms.Elementwise

namespace PoincareConjecture.M35.Uniqueness

open DeTurckNative

variable {n : ℕ}



theorem native_deTurck_difference (background : MetricJet2 (n := n))
    (p q : MetricLowerJet n) (Q S : MetricSecondJet n)
    (hp : p.1.PosDef) (hq : q.1.PosDef)
    (hQm : ∀ a b i j, Q a b i j = Q a b j i)
    (hQd : ∀ a b i j, Q a b i j = Q b a i j)
    (hSm : ∀ a b i j, S a b i j = S a b j i)
    (hSd : ∀ a b i j, S a b i j = S b a i j) (i j : Fin n) :
    chartStateSource background (lowerJetState p Q) i j -
        chartStateSource background (lowerJetState q S) i j -
        lowerJetContraction p.1⁻¹ (Q - S) i j =
      lowerJetContraction (p.1⁻¹ - q.1⁻¹) S i j +
        (lowerJetSource background p i j - lowerJetSource background q i j) := by
  have h := fixedPrincipalRemainder_sub background p q Q S hp hq hQm hQd hSm hSd
  have hij := congrFun (congrFun h i) j
  simp only [lowerJetContraction_sub_left, lowerJetContraction_sub_right,
    Matrix.sub_apply, Matrix.add_apply, fixedPrincipalRemainder] at hij ⊢
  linarith only [hij]




theorem exists_native_deTurck_difference_bound
    (B : Set (ChartState (n := n))) (K : Set (MetricLowerJet n))
    (hBconv : Convex ℝ B) (hBcompact : IsCompact B)
    (hBpos : ∀ b ∈ B, b.1.PosDef)
    (hKconv : Convex ℝ K) (hKcompact : IsCompact K)
    (hKpos : ∀ p ∈ K, p.1.PosDef) {H : ℝ} (hH : 0 ≤ H) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ b ∈ B, ∀ p ∈ K, ∀ q ∈ K,
      ∀ Q S : MetricSecondJet n,
      (∀ a b i j, Q a b i j = Q a b j i) →
      (∀ a b i j, Q a b i j = Q b a i j) →
      (∀ a b i j, S a b i j = S a b j i) →
      (∀ a b i j, S a b i j = S b a i j) →
      ‖S‖ ≤ H →
      ‖(fun i j => chartStateSource (chartStateJet b) (lowerJetState p Q) i j -
        chartStateSource (chartStateJet b) (lowerJetState q S) i j -
        lowerJetContraction p.1⁻¹ (Q - S) i j : Matrix (Fin n) (Fin n) ℝ)‖ ≤
          D * ‖p - q‖ := by
  obtain ⟨LI, _, hI, _⟩ := exists_lowerJet_coefficient_bounds
    (chartStateJet (0 : ChartState (n := n))) K hKconv hKcompact hKpos
  have hc : ContDiffOn ℝ 1
      (fun z : ChartState (n := n) × MetricLowerJet n =>
        lowerJetSource (chartStateJet z.1) z.2) (B ×ˢ K) := by
    intro z hz
    exact ((DeTurckMetricProducerNative.contDiffAt_jointLowerJetSource_infty z
      (hBpos z.1 hz.1) (hKpos z.2 hz.2)).of_le (by simp)).contDiffWithinAt
  obtain ⟨L, hL⟩ := hc.exists_lipschitzOnWith one_ne_zero
    (hBconv.prod hKconv) (hBcompact.prod hKcompact)
  refine ⟨(n : ℝ) ^ 2 * (LI : ℝ) * H + L, by positivity, ?_⟩
  intro b hb p hp q hq Q S hQm hQd hSm hSd hS
  have heq : (fun i j => chartStateSource (chartStateJet b) (lowerJetState p Q) i j -
      chartStateSource (chartStateJet b) (lowerJetState q S) i j -
      lowerJetContraction p.1⁻¹ (Q - S) i j : Matrix (Fin n) (Fin n) ℝ) =
      lowerJetContraction (p.1⁻¹ - q.1⁻¹) S +
        (lowerJetSource (chartStateJet b) p - lowerJetSource (chartStateJet b) q) := by
    ext i j
    exact native_deTurck_difference _ p q Q S (hKpos p hp) (hKpos q hq)
      hQm hQd hSm hSd i j
  rw [heq]
  have hlow : ‖lowerJetSource (chartStateJet b) p -
      lowerJetSource (chartStateJet b) q‖ ≤ (L : ℝ) * ‖p - q‖ := by
    simpa [dist_eq_norm, Prod.norm_def]
      using hL.dist_le_mul (b, p) ⟨hb, hp⟩ (b, q) ⟨hb, hq⟩
  calc
    _ ≤ ‖lowerJetContraction (p.1⁻¹ - q.1⁻¹) S‖ +
        ‖lowerJetSource (chartStateJet b) p - lowerJetSource (chartStateJet b) q‖ :=
      norm_add_le _ _
    _ ≤ (n : ℝ) ^ 2 * ((LI : ℝ) * ‖p - q‖) * H + (L : ℝ) * ‖p - q‖ := by
      apply add_le_add _ hlow
      exact (norm_lowerJetContraction_le _ _).trans
        (mul_le_mul (mul_le_mul_of_nonneg_left (hI p hp q hq) (sq_nonneg _))
          hS (norm_nonneg S) (by positivity))
    _ = _ := by ring

end PoincareConjecture.M35.Uniqueness
