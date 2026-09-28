import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.Basis
import Mathlib.LinearAlgebra.Determinant









set_option autoImplicit false

open Set

namespace AffineBasis

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E]

private theorem det_update_basis [Fintype ι] [DecidableEq ι]
    (e : Module.Basis ι ℝ E) (i : ι) (v : E) :
    e.det (Function.update e i v) = e.coord i v := by
  have hcoord : e.det.toMultilinearMap.toLinearMap e i = e.coord i := by
    apply e.ext
    intro k
    by_cases hki : k = i
    · subst k
      simp [MultilinearMap.toLinearMap_apply, Module.Basis.det_self,
        Module.Basis.coord_apply]
    · change e.det (Function.update e i (e k)) = e.coord i (e k)
      rw [e.det.map_update_self e (Ne.symm hki)]
      simp [Module.Basis.coord_apply, hki]
  exact congrArg (fun L : E →ₗ[ℝ] ℝ => L v) hcoord




theorem det_linear_eq_coord_of_fix_facet [Finite ι] (b : AffineBasis ι ℝ E)
    (i j : ι) (hij : i ≠ j) (T : E →ᵃ[ℝ] E)
    (hfix : ∀ k, k ≠ i → T (b k) = b k) :
    LinearMap.det T.linear = b.coord i (T (b i)) := by
  classical
  let := Fintype.ofFinite ι
  let e := b.basisOf j
  let ii : {k : ι // k ≠ j} := ⟨i, hij⟩
  have hcoord : (b.coord i).linear = e.coord ii := by
    apply e.ext
    intro k
    calc
      (b.coord i).linear (e k) = b.coord i (b k.val) - b.coord i (b j) := by
        simpa only [e, basisOf_apply, vsub_eq_sub] using
          (b.coord i).linearMap_vsub (b k.val) (b j)
      _ = if i = k.val then 1 else 0 := by
        rw [b.coord_apply_ne hij, sub_zero, b.coord_apply]
      _ = e.coord ii (e k) := by
        by_cases hik : i = k.val
        · have hk : k = ii := Subtype.ext hik.symm
          subst k
          simp [ii, Module.Basis.coord_apply]
        · have hki : k ≠ ii := fun h => hik (congrArg Subtype.val h).symm
          simp [hik, hki, Module.Basis.coord_apply]
  have hfamily : T.linear ∘ e = Function.update e ii (T.linear (e ii)) := by
    funext k
    by_cases hki : k = ii
    · subst k
      simp
    · rw [Function.update_of_ne hki]
      simp only [Function.comp_apply, e, basisOf_apply]
      rw [T.linearMap_vsub, hfix j (Ne.symm hij)]
      rw [hfix k.val (fun h => hki (Subtype.ext h))]
  calc
    LinearMap.det T.linear = e.det (T.linear ∘ e) := by
      rw [e.det_comp, e.det_self, mul_one]
    _ = e.coord ii (T.linear (e ii)) := by
      rw [hfamily, det_update_basis]
    _ = b.coord i (T (b i)) := by
      rw [← hcoord]
      simp only [e, basisOf_apply, ii]
      rw [T.linearMap_vsub, hfix j (Ne.symm hij), (b.coord i).linearMap_vsub,
        b.coord_apply_ne hij]
      simp

end AffineBasis
