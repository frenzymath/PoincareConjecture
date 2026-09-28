import PoincareConjecture.Proofs.M35.Uniqueness.Heat.JetExpressionBound









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap LineDeriv

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative DeTurckHigherDomainNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

def principalDifferenceSource (A B : Fin n → Fin n → 𝓢(V, ℝ))
    (p : List (Fin n) → L2) : L2 :=
  ∑ i, ∑ j, (schwartzMultiplier (A i j - B i j) (p [j, i]) +
    schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} (A i j - B i j)) (p [i]))

theorem divergence_equation_sub (A B : Fin n → Fin n → 𝓢(V, ℝ))
    (q p : List (Fin n) → L2) {G H : L2} {U : Set V}
    (hp : IsWeakSchwartzJet p 2)
    (hqeq : DivergenceEquation A (fun i => q [i]) G U)
    (hpeq : DivergenceEquation B (fun i => p [i]) H U) :
    DivergenceEquation A (fun i => q [i] - p [i])
      (G - H + principalDifferenceSource A B p) U := by
  intro φ hφ hφU
  have hdiff (i j : Fin n) :=
    (hp [i] (by simp) j).mul _ _ _ (A i j - B i j) φ
  have hsum := congrArg (fun f : Fin n → Fin n → ℝ => ∑ i, ∑ j, f i j)
    (funext (fun i => funext (fun j => hdiff i j)))
  have hmult (i j : Fin n) :
      schwartzMultiplier (A i j - B i j) (p [i]) =
        schwartzMultiplier (A i j) (p [i]) - schwartzMultiplier (B i j) (p [i]) := by
    apply Lp.ext
    filter_upwards [schwartzMultiplier_coe (A i j - B i j) (p [i]),
      schwartzMultiplier_coe (A i j) (p [i]), schwartzMultiplier_coe (B i j) (p [i]),
      Lp.coeFn_sub (schwartzMultiplier (A i j) (p [i]))
        (schwartzMultiplier (B i j) (p [i]))] with x hab ha hb hsub
    rw [hab, hsub, Pi.sub_apply, ha, hb, sub_apply, sub_mul]
  simp only [inner_add_left, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    hmult, inner_sub_left, Finset.sum_sub_distrib] at hsum
  have hq' := hqeq φ hφ hφU
  have hp' := hpeq φ hφ hφU
  simp only [map_sub, inner_sub_left, Finset.sum_sub_distrib, inner_add_left,
    principalDifferenceSource, sum_inner, Finset.sum_add_distrib]
  linarith only [hsum, hq', hp']

theorem norm_principalDifferenceSource_le (A B : Fin n → Fin n → 𝓢(V, ℝ))
    (p : List (Fin n) → L2) {c M : ℝ} (hc : 0 ≤ c)
    (hAB : ∀ i j, ‖schwartzMultiplier (A i j - B i j)‖ ≤ c)
    (hdAB : ∀ i j,
      ‖schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} (A i j - B i j))‖ ≤ c)
    (hp : ∀ i j, ‖p [i]‖ ≤ M ∧ ‖p [j, i]‖ ≤ M) :
    ‖principalDifferenceSource A B p‖ ≤ 2 * (n : ℝ) ^ 2 * c * M := by
  have hterm (i j : Fin n) :
      ‖schwartzMultiplier (A i j - B i j) (p [j, i]) +
        schwartzMultiplier (∂_{EuclideanSpace.single j (1 : ℝ)} (A i j - B i j)) (p [i])‖
        ≤ 2 * (c * M) := by
    have h1 := ((schwartzMultiplier (A i j - B i j)).le_opNorm (p [j, i])).trans
      ((mul_le_mul_of_nonneg_right (hAB i j) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hp i j).2 hc))
    have h2 := ((schwartzMultiplier
      (∂_{EuclideanSpace.single j (1 : ℝ)} (A i j - B i j))).le_opNorm (p [i])).trans
      ((mul_le_mul_of_nonneg_right (hdAB i j) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hp i j).1 hc))
    exact (norm_add_le _ _).trans (by linarith only [h1, h2])
  calc
    ‖principalDifferenceSource A B p‖ ≤ ∑ i, ∑ j, 2 * (c * M) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ =>
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm i j))
    _ = 2 * (n : ℝ) ^ 2 * c * M := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end PoincareConjecture.M35.Uniqueness.Heat
