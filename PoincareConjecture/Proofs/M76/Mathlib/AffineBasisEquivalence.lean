import Mathlib.LinearAlgebra.AffineSpace.Basis
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv










set_option autoImplicit false

open Affine




theorem AffineBasis.exists_affineEquiv_map {ι K V W P Q : Type*}
    [Ring K] [AddCommGroup V] [Module K V] [AffineSpace V P]
    [AddCommGroup W] [Module K W] [AffineSpace W Q]
    (b : AffineBasis ι K P) (c : AffineBasis ι K Q) (i₀ : ι) :
    ∃ e : P ≃ᵃ[K] Q, ∀ i, e (b i) = c i := by
  classical
  let L := (b.basisOf i₀).equiv (c.basisOf i₀) (Equiv.refl _)
  let e : P ≃ᵃ[K] Q := (AffineEquiv.vaddConst K (b i₀)).symm.trans
    (L.toAffineEquiv.trans (AffineEquiv.vaddConst K (c i₀)))
  refine ⟨e, ?_⟩
  intro i
  change L (b i -ᵥ b i₀) +ᵥ c i₀ = c i
  by_cases hi : i = i₀
  · subst i
    simp only [vsub_self, map_zero, zero_vadd]
  · rw [← b.basisOf_apply i₀ ⟨i, hi⟩]
    change (b.basisOf i₀).equiv (c.basisOf i₀) (Equiv.refl _) (b.basisOf i₀ ⟨i, hi⟩)
      +ᵥ c i₀ = c i
    rw [Module.Basis.equiv_apply]
    simp only [Equiv.refl_apply, AffineBasis.basisOf_apply, vsub_vadd]
