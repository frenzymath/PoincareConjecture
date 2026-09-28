import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.TimeSegmentsIntegral

set_option autoImplicit false

noncomputable section

open Set MeasureTheory

namespace PoincareConjecture.M35.Uniqueness.Heat.ValueInitial

theorem joinTime_integral_equation {E F : Type*} (Q : F → ℝ) (B : ℝ → E → ℝ)
    {r S T : ℝ} (hS : 0 ≤ S) (hT : 0 ≤ T) {u₀ : F}
    {v₁ v₂ : ℝ → E} {U₁ U₂ : ℝ → F}
    (h₁ : ∀ t ∈ Icc 0 S, Q (U₁ t) = Q u₀ + ∫ s in (0 : ℝ)..t, B (r + s) (v₁ s))
    (h₂ : ∀ t ∈ Icc 0 T, Q (U₂ t) = Q (U₁ S) +
      ∫ s in (0 : ℝ)..t, B ((r + S) + s) (v₂ s))
    (hf : IntervalIntegrable (fun s => B (r + s) (v₁ s)) volume 0 S)
    (hg : IntervalIntegrable (fun s => B ((r + S) + s) (v₂ s)) volume 0 T) :
    ∀ t ∈ Icc 0 (S + T), Q (joinTime U₁ U₂ S t) = Q u₀ +
      ∫ s in (0 : ℝ)..t, B (r + s) (joinTime v₁ v₂ S s) := by
  let f : ℝ → ℝ := fun s => B (r + s) (v₁ s)
  let g : ℝ → ℝ := fun s => B ((r + S) + s) (v₂ s)
  have heq : (fun s => B (r + s) (joinTime v₁ v₂ S s)) = joinTime f g S := by
    funext s
    by_cases hs : s ≤ S
    · simp only [joinTime, if_pos hs, f]
    · simp only [joinTime, if_neg hs, g]
      rw [show r + S + (s - S) = r + s by ring]
  intro t ht
  rw [heq]
  by_cases htS : t ≤ S
  · rw [integral_joinTime_left f g ht.1 htS, joinTime, if_pos htS]
    exact h₁ t ⟨ht.1, htS⟩
  · have hSt : S ≤ t := le_of_not_ge htS
    have ht' : t - S ∈ Icc 0 T := by
      constructor <;> linarith only [hSt, ht.2]
    have hgi : IntervalIntegrable g volume 0 (t - S) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht'.1).mpr
        (((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hg).mono_set
          (Ioc_subset_Ioc le_rfl ht'.2))
    rw [integral_joinTime_right f g hS hSt hf hgi, joinTime, if_neg htS]
    have hval₂ : Q (U₂ (t - S)) = Q (U₁ S) + ∫ s in (0 : ℝ)..(t - S), g s :=
      h₂ (t - S) ht'
    have hval₁ : Q (U₁ S) = Q u₀ + ∫ s in (0 : ℝ)..S, f s := h₁ S ⟨hS, le_rfl⟩
    rw [hval₂, hval₁]
    ring

end PoincareConjecture.M35.Uniqueness.Heat.ValueInitial
