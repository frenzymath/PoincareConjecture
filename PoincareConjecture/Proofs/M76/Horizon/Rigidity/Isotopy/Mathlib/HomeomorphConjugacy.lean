import Mathlib.Topology.Homotopy.Basic

set_option autoImplicit false

open Set

namespace ContinuousMap.HomotopyRel

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def of_homeomorph_conjugacy
    {f₀ f₁ : C(Y, Y)} {g₀ g₁ : C(X, X)} {S : Set Y}
    (F : f₀.HomotopyRel f₁ S) (h : X ≃ₜ Y)
    (h₀ : ∀ x, h (g₀ x) = f₀ (h x))
    (h₁ : ∀ x, h (g₁ x) = f₁ (h x)) :
    g₀.HomotopyRel g₁ (h ⁻¹' S) where
  toFun z := h.symm (F (z.1, h z.2))
  continuous_toFun := h.symm.continuous.comp
    (F.continuous.comp (continuous_fst.prodMk (h.continuous.comp continuous_snd)))
  map_zero_left x := by
    rw [F.apply_zero, ← h₀, h.symm_apply_apply]
  map_one_left x := by
    rw [F.apply_one, ← h₁, h.symm_apply_apply]
  prop' t x hx := by
    change h.symm (F (t, h x)) = g₀ x
    rw [F.eq_fst t hx, ← h₀, h.symm_apply_apply]

theorem of_homeomorph_conjugacy_apply
    {f₀ f₁ : C(Y, Y)} {g₀ g₁ : C(X, X)} {S : Set Y}
    (F : f₀.HomotopyRel f₁ S) (h : X ≃ₜ Y)
    (h₀ : ∀ x, h (g₀ x) = f₀ (h x))
    (h₁ : ∀ x, h (g₁ x) = f₁ (h x)) (t : unitInterval) (x : X) :
    F.of_homeomorph_conjugacy h h₀ h₁ (t, x) = h.symm (F (t, h x)) := rfl

end ContinuousMap.HomotopyRel

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem preimage_fixedSet_of_conjugacy (h : X ≃ₜ Y)
    {f : Y → Y} {g : X → X} {S : Set Y}
    (hf : f ⁻¹' S = S) (hmap : ∀ x, h (g x) = f (h x)) :
    g ⁻¹' (h ⁻¹' S) = h ⁻¹' S := by
  ext x
  change h (g x) ∈ S ↔ h x ∈ S
  rw [hmap]
  exact Iff.of_eq (congrArg (fun T : Set Y => h x ∈ T) hf)

end Homeomorph
