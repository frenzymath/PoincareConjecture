import PoincareConjecture.Proofs.M76.Triangulation.FinitePLSphereSections
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveInduction











set_option autoImplicit false

open Set Geometry

namespace Geometry.AlexanderSectionProfile

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]






theorem hasDisjointPolygonPresentation_of_sphere_model
    (W : AlexanderSectionProfile E) {D : Set F}
    {e : W.carrier ≃ₜ frontier D} (he : e.IsFinitePL)
    (hD : IsCompact D) (hcv : Convex ℝ D) (hne : (interior D).Nonempty)
    (hdim : Module.finrank ℝ F = 3) {c : ℝ} (hcharge : W.charge c = 0)
    (hsigns : ∀ x ∈ W.carrier, W.height x = c →
      x ∈ closure (W.carrier ∩ {y | W.height y < c}) ∧
        x ∈ closure (W.carrier ∩ {y | c < W.height y})) :
    HasDisjointPolygonPresentation (W.carrier ∩ {x | W.height x = c}) := by
  let B : E →ᵃ[ℝ] ℝ := W.height - AffineMap.const ℝ E c
  have hB (x : E) : B x = W.height x - c := rfl
  have hpres : HasAlexanderCurvePresentation (W.carrier ∩ {x | B x = 0}) 0 := by
    simpa only [hB, sub_eq_zero, hcharge] using W.presentation c
  have hsignsB : ∀ x ∈ W.carrier, B x = 0 →
      x ∈ closure (W.carrier ∩ {y | 0 < B y}) ∧
        x ∈ closure (W.carrier ∩ {y | B y < 0}) := by
    intro x hx hxB
    have hxc : W.height x = c := sub_eq_zero.mp (hB x ▸ hxB)
    obtain ⟨hlo, hhi⟩ := hsigns x hx hxc
    constructor
    · simpa only [hB, sub_pos] using hhi
    · simpa only [hB, sub_neg] using hlo
  simpa only [hB, sub_eq_zero] using
    he.hasDisjointPolygonPresentation_of_zero_charge_signs hD hcv hne hdim B hpres hsignsB





theorem finite_exceptional_regular_sections
    (W : AlexanderSectionProfile E) {D : Set F}
    {e : W.carrier ≃ₜ frontier D} (he : e.IsFinitePL)
    (hD : IsCompact D) (hcv : Convex ℝ D) (hne : (interior D).Nonempty)
    (hdim : Module.finrank ℝ F = 3) {C : Set ℝ} (hC : C.Finite)
    (hsigns : ∀ x ∈ W.carrier, W.height x ∉ C →
      x ∈ closure (W.carrier ∩ {y | W.height y < W.height x}) ∧
        x ∈ closure (W.carrier ∩ {y | W.height x < W.height y})) :
    (C ∪ Function.support W.charge).Finite ∧
      ∀ c : ℝ, c ∉ C ∪ Function.support W.charge →
        HasDisjointPolygonPresentation (W.carrier ∩ {x | W.height x = c}) := by
  refine ⟨hC.union W.finite_support, ?_⟩
  intro c hc
  have hcC : c ∉ C := fun h => hc (Or.inl h)
  have hcharge : W.charge c = 0 := by
    by_contra h
    exact hc (Or.inr h)
  apply W.hasDisjointPolygonPresentation_of_sphere_model he hD hcv hne hdim hcharge
  intro x hx hxc
  have h := hsigns x hx (by rwa [hxc])
  simpa only [hxc] using h

end Geometry.AlexanderSectionProfile
