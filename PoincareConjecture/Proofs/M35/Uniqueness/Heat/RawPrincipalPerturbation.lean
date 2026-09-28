import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawTimePrincipal
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawPrincipalExtension
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalFormOperator










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped SchwartzMap Matrix.Norms.Elementwise

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

def rawCutoffPrincipalCoefficient (g : RiemannianMetric n V)
    (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (i j : Fin n) : 𝓢(V, ℝ) :=
  EuclideanDerivativeNative.cutoffSchwartz η hη isOpen_univ (subset_univ _)
    (fun x => (rawCoordinateGram g x)⁻¹ i j)
    (raw_inverseGram_entry_contDiff g i j).contDiffOn

@[simp] theorem rawCutoffPrincipalCoefficient_apply (g : RiemannianMetric n V)
    (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (i j : Fin n) (x : V) :
    rawCutoffPrincipalCoefficient g η hη i j x = η x * (rawCoordinateGram g x)⁻¹ i j := rfl

theorem rawCutoffPrincipalCoefficient_difference_le (g h : RiemannianMetric n V)
    (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (hη1 : ∀ x, ‖η x‖ ≤ 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hdiff : ∀ x ∈ tsupport η,
      ‖(rawCoordinateGram g x)⁻¹ - (rawCoordinateGram h x)⁻¹‖ ≤ ε) :
    ∀ i j x, ‖rawCutoffPrincipalCoefficient g η hη i j x -
      rawCutoffPrincipalCoefficient h η hη i j x‖ ≤ ε := by
  intro i j x
  rw [rawCutoffPrincipalCoefficient_apply, rawCutoffPrincipalCoefficient_apply,
    ← mul_sub, norm_mul]
  by_cases hx : η x = 0
  · simpa only [hx, norm_zero, zero_mul] using hε
  · have hxs : x ∈ tsupport η := subset_closure hx
    let M := (rawCoordinateGram g x)⁻¹ - (rawCoordinateGram h x)⁻¹
    have he : ‖M i j‖ ≤ ‖M‖ := (norm_le_pi_norm (M i) j).trans (norm_le_pi_norm M i)
    have heps : ‖(rawCoordinateGram g x)⁻¹ i j - (rawCoordinateGram h x)⁻¹ i j‖ ≤ ε :=
      he.trans (hdiff x hxs)
    exact (mul_le_mul (hη1 x) heps (norm_nonneg _) zero_le_one).trans_eq (one_mul _)



theorem exists_raw_small_principal_form_perturbation {J : Set ℝ} (F : RicciFlow n V J)
    {a b : ℝ} (hab : a < b) (hJ : Icc a b ⊆ J)
    (K : Set V) (η : 𝓢(V, ℝ)) (hη : HasCompactSupport η) (hη1 : ∀ x, ‖η x‖ ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ a + τ < b ∧ ∀ t ∈ Icc a (a + τ),
      ‖principalFormOperator K (rawCutoffPrincipalCoefficient (F.metric t) η hη) -
        principalFormOperator K (rawCutoffPrincipalCoefficient (F.metric a) η hη)‖ ≤ ε := by
  let d := (n : ℝ) ^ 2 + 1
  have hd : 0 < d := by dsimp only [d]; positivity
  obtain ⟨τ, hτ, hτb, hclose⟩ := exists_raw_principal_small_time_change F hab hJ hη
    (div_pos hε hd)
  refine ⟨τ, hτ, hτb, ?_⟩
  intro t ht
  have hc := rawCutoffPrincipalCoefficient_difference_le (F.metric t) (F.metric a)
    η hη hη1 (div_nonneg hε.le hd.le) (fun x hx => (hclose t ht x hx).le)
  calc
    _ ≤ (n : ℝ) ^ 2 * (ε / d) :=
      norm_principalFormOperator_sub_le K _ _ (div_nonneg hε.le hd.le) hc
    _ ≤ d * (ε / d) := mul_le_mul_of_nonneg_right (by dsimp only [d]; linarith)
      (div_nonneg hε.le hd.le)
    _ = ε := mul_div_cancel₀ ε hd.ne'

end PoincareConjecture.M35.Uniqueness.Heat
