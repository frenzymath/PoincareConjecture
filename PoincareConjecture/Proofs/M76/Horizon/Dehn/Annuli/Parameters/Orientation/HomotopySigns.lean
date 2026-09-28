import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.CircleHomeomorphLift









set_option autoImplicit false
open Set unitInterval

namespace AddCircle

variable {p : ℝ} [Fact (0 < p)]

omit [Fact (0 < p)] in

theorem lift_period_displacement_eq_of_homotopy
    (q₀ q₁ : C(AddCircle p, AddCircle p)) (H : q₀.Homotopy q₁)
    (L₀ L₁ : C(ℝ, ℝ))
    (hL₀ : ∀ t, (L₀ t : AddCircle p) = q₀ (t : AddCircle p))
    (hL₁ : ∀ t, (L₁ t : AddCircle p) = q₁ (t : AddCircle p)) :
    L₀ p - L₀ 0 = L₁ p - L₁ 0 := by
  let F : C(I × ℝ, AddCircle p) :=
    H.toContinuousMap.comp ⟨fun z ↦ (z.1, (z.2 : AddCircle p)), by fun_prop⟩
  have hF₀ (x : ℝ) : F (0, x) = (L₀ x : AddCircle p) :=
    (H.apply_zero _).trans (hL₀ x).symm
  let cov := isCoveringMap_coe p
  let G := cov.liftHomotopy F L₀ hF₀
  have hG (t : I) (x : ℝ) : (G (t, x) : AddCircle p) = H (t, (x : AddCircle p)) :=
    congrFun (cov.liftHomotopy_lifts F L₀ hF₀) (t, x)
  have hG₀ (x : ℝ) : G (0, x) = L₀ x := cov.liftHomotopy_zero F L₀ hF₀ x
  have hdisplacement : G (1, p) - G (1, 0) = G (0, p) - G (0, 0) := by
    apply cov.const_of_comp (g := fun t : I ↦ G (t, p) - G (t, 0))
      (by fun_prop) _ 1 0
    intro t u
    simp only [coe_sub, hG, coe_period, coe_zero, sub_self]
  have hphase : G (1, p) - L₁ p = G (1, 0) - L₁ 0 := by
    apply cov.const_of_comp (g := fun x : ℝ ↦ G (1, x) - L₁ x) (by fun_prop) _ p 0
    intro x y
    simp only [coe_sub, hG, H.apply_one, hL₁, sub_self]
  rw [hG₀, hG₀] at hdisplacement
  linarith

omit [Fact (0 < p)] in

theorem interval_lift_displacement_eq_of_homotopy
    (q₀ q₁ : C(AddCircle p, AddCircle p)) (H : q₀.Homotopy q₁)
    (L₀ L₁ : C(I, ℝ))
    (hL₀ : ∀ t, (L₀ t : AddCircle p) = q₀ ((p * (t : ℝ) : ℝ) : AddCircle p))
    (hL₁ : ∀ t, (L₁ t : AddCircle p) = q₁ ((p * (t : ℝ) : ℝ) : AddCircle p)) :
    L₀ 1 - L₀ 0 = L₁ 1 - L₁ 0 := by
  let F : C(I × I, AddCircle p) := H.toContinuousMap.comp
    ⟨fun z ↦ (z.1, ((p * (z.2 : ℝ) : ℝ) : AddCircle p)), by fun_prop⟩
  have hF₀ (x : I) : F (0, x) = (L₀ x : AddCircle p) :=
    (H.apply_zero _).trans (hL₀ x).symm
  let cov := isCoveringMap_coe p
  let G := cov.liftHomotopy F L₀ hF₀
  have hG (t x : I) : (G (t, x) : AddCircle p) =
      H (t, ((p * (x : ℝ) : ℝ) : AddCircle p)) :=
    congrFun (cov.liftHomotopy_lifts F L₀ hF₀) (t, x)
  have hG₀ (x : I) : G (0, x) = L₀ x := cov.liftHomotopy_zero F L₀ hF₀ x
  have hd : G (1, 1) - G (1, 0) = G (0, 1) - G (0, 0) := by
    apply cov.const_of_comp (g := fun t : I ↦ G (t, 1) - G (t, 0)) (by fun_prop) _ 1 0
    intro t u
    simp only [coe_sub, hG]
    change H (t, ((p * 1 : ℝ) : AddCircle p)) - H (t, ((p * 0 : ℝ) : AddCircle p)) =
      H (u, ((p * 1 : ℝ) : AddCircle p)) - H (u, ((p * 0 : ℝ) : AddCircle p))
    simp only [mul_one, mul_zero, coe_period, coe_zero, sub_self]
  have hphase : G (1, 1) - L₁ 1 = G (1, 0) - L₁ 0 := by
    apply cov.const_of_comp (g := fun x : I ↦ G (1, x) - L₁ x) (by fun_prop) _ 1 0
    intro x y
    simp only [coe_sub, hG, H.apply_one, hL₁, sub_self]
  rw [hG₀, hG₀] at hd
  linarith



theorem signed_interval_formulas_same_sign
    (q₀ q₁ : C(AddCircle p, AddCircle p)) (H : q₀.Homotopy q₁)
    (b₀ b₁ : ℝ) (positive₀ positive₁ : Bool) (e₀ e₁ : C(I, I))
    (he₀0 : (e₀ 0 : ℝ) = 0) (he₀1 : (e₀ 1 : ℝ) = 1)
    (he₁0 : (e₁ 0 : ℝ) = 0) (he₁1 : (e₁ 1 : ℝ) = 1)
    (h₀ : ∀ t : I, q₀ ((p * (t : ℝ) : ℝ) : AddCircle p) =
      ((b₀ + (if positive₀ then p * (e₀ t : ℝ) else -(p * (e₀ t : ℝ))) : ℝ) : AddCircle p))
    (h₁ : ∀ t : I, q₁ ((p * (t : ℝ) : ℝ) : AddCircle p) =
      ((b₁ + (if positive₁ then p * (e₁ t : ℝ) else -(p * (e₁ t : ℝ))) : ℝ) : AddCircle p)) :
    positive₀ = positive₁ := by
  let L₀ : C(I, ℝ) :=
    ⟨fun t ↦ b₀ + (if positive₀ then p * (e₀ t : ℝ) else -(p * (e₀ t : ℝ))),
      by cases positive₀ <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop⟩
  let L₁ : C(I, ℝ) :=
    ⟨fun t ↦ b₁ + (if positive₁ then p * (e₁ t : ℝ) else -(p * (e₁ t : ℝ))),
      by cases positive₁ <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop⟩
  have h := interval_lift_displacement_eq_of_homotopy q₀ q₁ H L₀ L₁
    (fun t ↦ (h₀ t).symm) (fun t ↦ (h₁ t).symm)
  have hp := Fact.out (p := 0 < p)
  simp only [L₀, L₁, ContinuousMap.coe_mk, he₀0, he₀1, he₁0, he₁1,
    mul_one, mul_zero, neg_zero, ite_self, add_zero] at h
  cases positive₀ <;> cases positive₁
  · rfl
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    linarith
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    linarith
  · rfl



theorem real_homeomorph_lifts_same_orientation_of_homotopy
    (q₀ q₁ : AddCircle p ≃ₜ AddCircle p)
    (H : (⟨q₀, q₀.continuous⟩ : C(AddCircle p, AddCircle p)).Homotopy
      ⟨q₁, q₁.continuous⟩)
    (L₀ L₁ : ℝ ≃ₜ ℝ)
    (hL₀ : ∀ t, (L₀ t : AddCircle p) = q₀ (t : AddCircle p))
    (hL₁ : ∀ t, (L₁ t : AddCircle p) = q₁ (t : AddCircle p)) :
    (StrictMono L₀ ∧ StrictMono L₁ ∧
      (∀ t, L₀ (t + p) = L₀ t + p) ∧ (∀ t, L₁ (t + p) = L₁ t + p)) ∨
    (StrictAnti L₀ ∧ StrictAnti L₁ ∧
      (∀ t, L₀ (t + p) = L₀ t - p) ∧ (∀ t, L₁ (t + p) = L₁ t - p)) := by
  have h := lift_period_displacement_eq_of_homotopy
    ⟨q₀, q₀.continuous⟩ ⟨q₁, q₁.continuous⟩ H
    ⟨L₀, L₀.continuous⟩ ⟨L₁, L₁.continuous⟩ hL₀ hL₁
  have hp := Fact.out (p := 0 < p)
  rcases real_homeomorph_lift_orientation q₀ L₀ hL₀ with ⟨hm₀, ht₀⟩ | ⟨hm₀, ht₀⟩
  · rcases real_homeomorph_lift_orientation q₁ L₁ hL₁ with ⟨hm₁, ht₁⟩ | ⟨hm₁, ht₁⟩
    · exact Or.inl ⟨hm₀, hm₁, ht₀, ht₁⟩
    · have h₀ := ht₀ 0
      have h₁ := ht₁ 0
      simp only [zero_add] at h₀ h₁
      change L₀ p - L₀ 0 = L₁ p - L₁ 0 at h
      linarith
  · rcases real_homeomorph_lift_orientation q₁ L₁ hL₁ with ⟨hm₁, ht₁⟩ | ⟨hm₁, ht₁⟩
    · have h₀ := ht₀ 0
      have h₁ := ht₁ 0
      simp only [zero_add] at h₀ h₁
      change L₀ p - L₀ 0 = L₁ p - L₁ 0 at h
      linarith
    · exact Or.inr ⟨hm₀, hm₁, ht₀, ht₁⟩

end AddCircle
