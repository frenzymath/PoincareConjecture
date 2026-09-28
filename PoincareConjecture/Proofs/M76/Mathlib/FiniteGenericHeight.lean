import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Polygon.Basic











set_option autoImplicit false

open Set




theorem Set.Finite.exists_linearMap_injOn {K E : Type*} [Field K] [Infinite K]
    [AddCommGroup E] [Module K E] {s : Set E} (hs : s.Finite) :
    ∃ L : E →ₗ[K] K, InjOn L s := by
  let : Finite s := hs.to_subtype
  let I := {p : s × s // p.1 ≠ p.2}
  let d : I → E := fun p => p.val.1.val - p.val.2.val
  have hd : ∀ p, d p ≠ 0 := fun p => sub_ne_zero.mpr
    (fun h => p.property (Subtype.ext h))
  obtain ⟨L, hL⟩ := Module.exists_dual_forall_apply_ne_zero (K := K) d hd
  refine ⟨L, ?_⟩
  intro x hx y hy hxy
  by_contra hne
  let p : I := ⟨(⟨x, hx⟩, ⟨y, hy⟩), fun h => hne (congrArg Subtype.val h)⟩
  have hp := hL p
  exact hp (by change L (x - y) = 0; rw [map_sub, hxy, sub_self])




theorem Set.Finite.exists_continuousLinearMap_injOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : s.Finite) : ∃ L : E →L[ℝ] ℝ, InjOn L s := by
  obtain ⟨L, hL⟩ := hs.exists_linearMap_injOn (K := ℝ)
  exact ⟨⟨L, L.continuous_of_finiteDimensional⟩, hL⟩




theorem Polygon.exists_strict_max_height {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ} (P : Polygon E (n + 3)) (hinj : Function.Injective P) :
    ∃ (L : E →ₗ[ℝ] ℝ) (i : Fin (n + 3)),
      Function.Injective (fun j => L (P j)) ∧ ∀ j, j ≠ i → L (P j) < L (P i) := by
  obtain ⟨L, hL⟩ := (finite_range P).exists_linearMap_injOn (K := ℝ)
  have hi : Function.Injective (fun j => L (P j)) :=
    fun i j hij => hinj (hL (mem_range_self i) (mem_range_self j) hij)
  obtain ⟨i, _, hmax⟩ := Finset.univ.exists_max_image (fun j => L (P j))
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin (n + 3))).Nonempty)
  exact ⟨L, i, hi, fun j hji => lt_of_le_of_ne (hmax j (Finset.mem_univ _))
    (fun h => hji (hi h))⟩
