import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Analysis.Normed.Module.FiniteDimension











set_option autoImplicit false

open Set Function

namespace PoincareConjecture.M25.Topology3D

section Algebra

variable {K V I : Type*} [Field K] [Infinite K] [AddCommGroup V] [Module K V]


theorem exists_linearMap_injective_comp_finite [Finite I] (v : I → V) (hv : Injective v) :
    ∃ f : V →ₗ[K] K, Injective (f ∘ v) := by
  classical
  let w : {ij : I × I // ij.1 ≠ ij.2} → V := fun ij => v ij.1.1 - v ij.1.2
  have hw : ∀ ij, w ij ≠ 0 := fun ij =>
    sub_ne_zero.mpr (fun heq => ij.2 (hv heq))
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := K) w hw
  refine ⟨f, fun i j hij => ?_⟩
  by_contra hne
  apply hf ⟨(i, j), hne⟩
  change f (v i - v j) = 0
  rw [map_sub, sub_eq_zero]
  exact hij


theorem exists_linearMap_injOn_finite {s : Set V} (hs : s.Finite) :
    ∃ f : V →ₗ[K] K, InjOn f s := by
  classical
  let := hs.fintype
  obtain ⟨f, hf⟩ := exists_linearMap_injective_comp_finite (K := K)
    (fun x : s => (x : V)) Subtype.val_injective
  refine ⟨f, fun x hx y hy hxy => ?_⟩
  exact congrArg Subtype.val (hf (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)

end Algebra



theorem exists_continuousLinearMap_injOn_finite {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : s.Finite) : ∃ f : E →L[ℝ] ℝ, InjOn f s := by
  obtain ⟨f, hf⟩ := exists_linearMap_injOn_finite (K := ℝ) hs
  exact ⟨f.toContinuousLinearMap, hf⟩

end PoincareConjecture.M25.Topology3D
