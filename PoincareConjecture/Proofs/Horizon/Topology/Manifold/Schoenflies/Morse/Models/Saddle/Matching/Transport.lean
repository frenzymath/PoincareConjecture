import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.HeightCoordinates
import Mathlib.Geometry.Manifold.Instances.Sphere

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev axis : E3 := EuclideanSpace.single 2 1

theorem exists_scaled_saddle_transport {v : E3} (hv : ‖v‖ = 1)
    (c : Real) {s : Real} (hs : 0 < s)
    (J₀ : E2 ≃ₗᵢ[Real] (Real ∙ axis)ᗮ) (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ) :
    ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y : E3, inner Real v (H y) = c+s*(y 2+1)) ∧
      ∀ (t : Real) (x : E2),
        H ((J₀ x : E3) + t • axis) =
          (J (Real.sqrt s • x) : E3) + (c+s*(t+1)) • v := by
  have hsqrt : Real.sqrt s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  let P : Diffeomorph 𝓘(Real, Real × E2) 𝓘(Real, Real × E2)
      (Real × E2) (Real × E2) ∞ := {
    toEquiv := {
      toFun := fun z => (c+s*(z.1+1), Real.sqrt s • z.2)
      invFun := fun z => ((z.1-c)/s-1, (Real.sqrt s)⁻¹ • z.2)
      left_inv := by
        intro z
        apply Prod.ext
        · dsimp
          field_simp [hs.ne']
          ring
        · simp [smul_smul, hsqrt]
      right_inv := by
        intro z
        apply Prod.ext
        · dsimp
          field_simp [hs.ne']
          ring
        · simp [smul_smul, hsqrt] }
    contMDiff_toFun := by
      apply ContDiff.contMDiff
      change ContDiff Real ∞ (fun z : Real × E2 =>
        (c+s*(z.1+1), Real.sqrt s • z.2))
      fun_prop
    contMDiff_invFun := by
      apply ContDiff.contMDiff
      change ContDiff Real ∞ (fun z : Real × E2 =>
        ((z.1-c)/s-1, (Real.sqrt s)⁻¹ • z.2))
      fun_prop }
  let L₀ : (Real × E2) ≃L[Real] E3 :=
    ((ContinuousLinearEquiv.refl Real Real).prodCongr J₀.toContinuousLinearEquiv).trans
      (Poincare.Geometry.Euclidean.heightCoordinates (show ‖axis‖ = 1 by simp [axis]))
  let L : (Real × E2) ≃L[Real] E3 :=
    ((ContinuousLinearEquiv.refl Real Real).prodCongr J.toContinuousLinearEquiv).trans
      (Poincare.Geometry.Euclidean.heightCoordinates hv)
  have hL (t : Real) (x : E2) : L (t, x) = t • v + (J x : E3) := rfl
  have hL₀ (t : Real) (x : E2) : L₀ (t, x) = t • axis + (J₀ x : E3) := rfl
  let H := (L₀.symm.toDiffeomorph.trans P).trans L.toDiffeomorph
  have hH (y : E3) : H y = L (P (L₀.symm y)) := rfl
  refine ⟨H, ?_, ?_⟩
  · intro y
    rw [hH]
    change inner Real v (L (c+s*((L₀.symm y).1+1), Real.sqrt s • (L₀.symm y).2)) = _
    rw [hL]
    have horth := Submodule.mem_orthogonal_singleton_iff_inner_right.mp
      (J (Real.sqrt s • (L₀.symm y).2)).property
    simp only [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,
      hv, one_pow, mul_one, horth, add_zero]
    have hfirst : (L₀.symm y).1 = y 2 := by
      change inner Real axis y = y 2
      simp [axis, PiLp.inner_apply]
    rw [hfirst]
  · intro t x
    rw [add_comm (J₀ x : E3), ← hL₀, hH, L₀.symm_apply_apply]
    change L (c+s*(t+1), Real.sqrt s • x) = _
    rw [hL, add_comm]

end Poincare.Manifold.Schoenflies.Saddle
