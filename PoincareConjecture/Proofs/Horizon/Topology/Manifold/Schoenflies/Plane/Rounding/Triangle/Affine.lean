import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.Triangle.Equilateral
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Normed.Module.FiniteDimension









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped ContDiff Manifold

namespace Poincare.Manifold.Schoenflies.Plane


theorem roundedVertexPath_affine {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (b : F)
    (ρ : ℝ → ℝ) (P : ℤ → E) (t : ℝ) :
    roundedVertexPath ρ (fun j => L (P j) + b) t = L (roundedVertexPath ρ P t) + b := by
  simp only [roundedVertexPath, roundedCorner, map_add, map_smul, map_sub]
  module

private theorem planeDet_basis_injective {a b : EuclideanSpace ℝ (Fin 2)}
    (h : planeDet a b ≠ 0) :
    Injective (fun z : ℂ => z.re • a + z.im • b) := by
  suffices hz : ∀ z : ℂ, z.re • a + z.im • b = 0 → z = 0 by
    intro z w hzw
    change z.re • a + z.im • b = w.re • a + w.im • b at hzw
    apply sub_eq_zero.mp
    apply hz
    simp only [Complex.sub_re, Complex.sub_im, sub_smul]
    rw [show z.re • a - w.re • a + (z.im • b - w.im • b) =
      (z.re • a + z.im • b) - (w.re • a + w.im • b) by module, hzw, sub_self]
  intro z hz
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hz
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) hz
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.zero_apply, smul_eq_mul] at h0 h1
  have hre : z.re * planeDet a b = 0 := by
    dsimp [planeDet]
    linear_combination b 1 * h0 - b 0 * h1
  have him : z.im * planeDet a b = 0 := by
    dsimp [planeDet]
    linear_combination a 0 * h1 - a 1 * h0
  apply Complex.ext <;> simp only [Complex.zero_re, Complex.zero_im]
  · exact (mul_eq_zero.mp hre).resolve_right h
  · exact (mul_eq_zero.mp him).resolve_right h



theorem exists_affine_diffeomorph_rounded_triangle
    (e : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (p : Polygon (EuclideanSpace ℝ (Fin 2)) 3)
    (hp : planeDet (p 1 - p 0) (p 2 - p 1) ≠ 0) :
    ∃ F : ℂ ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 2),
      ∀ ρ : ℝ → ℝ, ∀ t : ℝ,
        F (roundedVertexPath ρ equilateralVertex t) = roundedPolygonParameter ρ p t := by
  let g := triangleBarycenter p
  let a := p 0 - g
  let b := (Real.sqrt 3)⁻¹ • (p 1 - p 2)
  have hsqrt : Real.sqrt (3 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hdet : planeDet a b = (2 / (3 * Real.sqrt 3)) *
      planeDet (p 1 - p 0) (p 2 - p 1) := by
    dsimp [a, b, g, triangleBarycenter, planeDet]
    field_simp
    ring
  have hdet0 : planeDet a b ≠ 0 := by rw [hdet]; exact mul_ne_zero (by positivity) hp
  let L : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    Complex.reCLM.smulRight a + Complex.imCLM.smulRight b
  have hL (z : ℂ) : L z = z.re • a + z.im • b := rfl
  have hinj : Injective L := planeDet_basis_injective hdet0
  have hsurj : Surjective L := by
    have h := LinearMap.surjective_of_injective
      (f := L.toLinearMap.comp e.symm.toLinearEquiv.toLinearMap) (hinj.comp e.symm.injective)
    intro x
    obtain ⟨y, hy⟩ := h x
    exact ⟨e.symm y, hy⟩
  let C : ℂ ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    (LinearEquiv.ofBijective L.toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  let F : ℂ ≃ₘ[ℝ] EuclideanSpace ℝ (Fin 2) :=
    { toEquiv :=
        { toFun := fun z => C z + g
          invFun := fun x => C.symm (x - g)
          left_inv := by intro z; simp
          right_inv := by intro x; simp }
      contMDiff_toFun := (C.contDiff.add contDiff_const).contMDiff
      contMDiff_invFun := (C.symm.contDiff.comp (contDiff_id.sub contDiff_const)).contMDiff }
  have hF (z : ℂ) : F z = L z + g := rfl
  have hcoeff : (Real.sqrt 3 / 2) * (Real.sqrt 3)⁻¹ = (1 / 2 : ℝ) := by field_simp
  have hvertex (k : Fin 3) : F (equilateralVertex (k.val : ℤ)) = p k := by
    fin_cases k
    · simp [hF, hL, equilateralVertex, a]
    · change F (equilateralVertex 1) = p 1
      rw [equilateralVertex_one, hF, hL]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im,
        mul_zero, mul_one, add_zero, zero_add, sub_zero]
      dsimp only [b]
      rw [smul_smul, hcoeff]
      dsimp [a, g, triangleBarycenter]
      module
    · change F (equilateralVertex 2) = p 2
      have h2 : equilateralVertex (2 : ℤ) = equilateralVertex (-1) := by
        simpa using periodic_equilateralVertex (-1)
      rw [h2, equilateralVertex_neg_one, hF, hL]
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, Complex.sub_im, Complex.mul_im,
        mul_zero, mul_one, sub_zero, add_zero, zero_sub]
      dsimp only [b]
      rw [neg_smul, smul_smul, hcoeff]
      dsimp [a, g, triangleBarycenter]
      module
  have hall (j : ℤ) : F (equilateralVertex j) = p (polygonIntegerIndex 3 j) := by
    have hmod : j - (j / 3) * 3 = j % 3 := by omega
    have hper := periodic_equilateralVertex.sub_int_mul_eq (j / 3) (x := j)
    simp only [Int.cast_id, hmod] at hper
    have hidx : ((polygonIntegerIndex 3 j).val : ℤ) = j % 3 := by
      change ((j % 3).toNat : ℤ) = j % 3
      exact Int.toNat_of_nonneg (Int.emod_nonneg j (by norm_num : (3 : ℤ) ≠ 0))
    rw [← hper, ← hidx]
    exact hvertex _
  refine ⟨F, fun ρ t => ?_⟩
  rw [hF, ← roundedVertexPath_affine L g ρ equilateralVertex t]
  change roundedVertexPath ρ (fun j => F (equilateralVertex j)) t = _
  simp only [hall, roundedPolygonParameter]

end Poincare.Manifold.Schoenflies.Plane
