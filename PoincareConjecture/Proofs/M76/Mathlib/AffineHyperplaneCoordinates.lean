import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas










set_option autoImplicit false

open Set

namespace AffineMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]




theorem exists_zeroLevel_coordinates (A : E →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F + 1) :
    ∃ (a : F →ᴬ[ℝ] E) (r : E →ᴬ[ℝ] F),
      Function.LeftInverse r a ∧ LeftInvOn a r {x | A x = 0} ∧
      ∀ y, A (a y) = 0 := by
  classical
  obtain ⟨p, hp⟩ := (A.linear_surjective_iff.mp (LinearMap.surjective hA)) 0
  have hker : Module.finrank ℝ F = Module.finrank ℝ A.linear.ker := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero hA
    omega
  let e : F ≃ₗ[ℝ] A.linear.ker := LinearEquiv.ofFinrankEq _ _ hker
  let i : F →ₗ[ℝ] E := A.linear.ker.subtype.comp e.toLinearMap
  have hi : Function.Injective i := Subtype.val_injective.comp e.injective
  obtain ⟨R, hR⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  have hRi (y : F) : R (i y) = y := LinearMap.congr_fun hR y
  let a₀ : F →ᵃ[ℝ] E := i.toAffineMap + AffineMap.const ℝ F p
  let r₀ : E →ᵃ[ℝ] F := R.toAffineMap - AffineMap.const ℝ E (R p)
  let a : F →ᴬ[ℝ] E := ⟨a₀, a₀.continuous_of_finiteDimensional⟩
  let r : E →ᴬ[ℝ] F := ⟨r₀, r₀.continuous_of_finiteDimensional⟩
  have hleft : Function.LeftInverse r a := by
    intro y
    change R (i y + p) - R p = y
    simp [map_add, hRi]
  refine ⟨a, r, hleft, ?_, ?_⟩
  · intro x hx
    change A x = 0 at hx
    have hxker : x - p ∈ A.linear.ker := by
      change A.linear (x - p) = 0
      simpa only [vsub_eq_sub, hx, hp, sub_self] using A.linearMap_vsub x p
    let z : A.linear.ker := ⟨x - p, hxker⟩
    have hximage : a (e.symm z) = x := by
      change (e (e.symm z) : E) + p = x
      simp [z]
    rw [← hximage, hleft]
  · intro y
    change A ((e y : E) + p) = 0
    have hy : A.linear (e y : E) = 0 := (e y).property
    simpa only [vadd_eq_add, hy, hp, add_zero] using A.map_vadd p (e y : E)

end AffineMap
