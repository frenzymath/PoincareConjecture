import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Arcs.Outermost



set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.Dehn.Annuli

theorem paired_returning_disks_intersection
    {E₀ E₁ X : Type*} (f₀ : E₀ → X) (f₁ : E₁ → X)
    {A₀ D₀ W₀ : Set E₀} {D₁ W₁ : Set E₁}
    (hD₀ : D₀ ⊆ A₀) (hW₀ : W₀ ⊆ D₀) (hW₁ : W₁ ⊆ D₁)
    (hi₀ : InjOn f₀ A₀)
    (htrace : D₁ ∩ f₁ ⁻¹' (f₀ '' A₀) = W₁)
    (hseam : f₀ '' W₀ = f₁ '' W₁) :
    (f₀ '' D₀) ∩ (f₁ '' D₁) = f₀ '' W₀ ∧
      ∀ (U₀ : Set E₀) (U₁ : Set E₁) (a b : E₀),
        U₀ ⊆ D₀ → U₁ ⊆ D₁ → U₀ ∩ W₀ = {a, b} →
        f₀ a ∈ f₁ '' U₁ → f₀ b ∈ f₁ '' U₁ →
        (f₀ '' U₀) ∩ (f₁ '' U₁) = {f₀ a, f₀ b} := by
  have hdisk : (f₀ '' D₀) ∩ (f₁ '' D₁) = f₀ '' W₀ := by
    apply Subset.antisymm
    · rintro y ⟨⟨x, hx, rfl⟩, z, hz, hzx⟩
      have hzW : z ∈ W₁ := htrace.subset ⟨hz, ⟨x, hD₀ hx, hzx.symm⟩⟩
      exact hseam.symm.subset ⟨z, hzW, hzx⟩
    · intro y hy
      exact ⟨image_mono hW₀ hy, image_mono hW₁ (hseam.subset hy)⟩
  refine ⟨hdisk, ?_⟩
  intro U₀ U₁ a b hU₀ hU₁ hends ha hb
  apply Subset.antisymm
  · rintro y ⟨⟨x, hx, rfl⟩, hy₁⟩
    obtain ⟨z, hz, hzx⟩ := hdisk.subset
      ⟨⟨x, hU₀ hx, rfl⟩, image_mono hU₁ hy₁⟩
    have hzx' : z = x := hi₀ (hD₀ (hW₀ hz)) (hD₀ (hU₀ hx)) hzx
    have hxends := hends.subset ⟨hx, hzx' ▸ hz⟩
    rcases hxends with rfl | rfl <;> simp
  · rintro y (rfl | rfl)
    · exact ⟨⟨a, (hends.symm.subset (by simp)).1, rfl⟩, ha⟩
    · exact ⟨⟨b, (hends.symm.subset (by simp)).1, rfl⟩, hb⟩

end PoincareConjecture.M76.Dehn.Annuli
