import PoincareConjecture.Proofs.M25.Topology3D.Plane.RetainedMidpointChain
import PoincareConjecture.Proofs.M25.Topology3D.Plane.RoundedPolygon
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def triangleComplexAffineMap (b : AffineBasis (Fin 3) ℝ E) : E →ᵃ[ℝ] ℂ :=
  Complex.equivRealProdCLM.symm.toLinearMap.toAffineMap.comp
    ((b.coord 1 - AffineMap.const ℝ E (1 / 3)).prod
      (b.coord 2 - AffineMap.const ℝ E (1 / 3)))

theorem triangleComplexAffineMap_apply (b : AffineBasis (Fin 3) ℝ E) (x : E) :
    triangleComplexAffineMap b x = ⟨b.coord 1 x - 1 / 3, b.coord 2 x - 1 / 3⟩ := rfl

theorem exists_triangle_coordinate_diffeomorph [FiniteDimensional ℝ E]
    (b : AffineBasis (Fin 3) ℝ E) :
    ∃ C : E ≃ₘ[ℝ] ℂ, ∀ x, C x = triangleComplexAffineMap b x := by
  let w : ℂ → Fin 3 → ℝ := fun z => ![1 / 3 - z.re - z.im, 1 / 3 + z.re, 1 / 3 + z.im]
  let J : ℂ → E := fun z => ∑ i : Fin 3, w z i • b i
  have hw (z : ℂ) : ∑ i : Fin 3, w z i = 1 := by
    simp [Fin.sum_univ_three, w]
    ring
  have hJcoord (z : ℂ) (i : Fin 3) : b.coord i (J z) = w z i := by
    change b.coord i (∑ j : Fin 3, w z j • b j) = w z i
    rw [← Finset.univ.affineCombination_eq_linear_combination _ _ (hw z)]
    exact b.coord_apply_combination_of_mem (Finset.mem_univ i) (hw z)
  have hCJ (z : ℂ) : triangleComplexAffineMap b (J z) = z := by
    apply Complex.ext <;> simp [triangleComplexAffineMap_apply, hJcoord, w]
  have hJC (x : E) : J (triangleComplexAffineMap b x) = x := by
    apply b.ext_elem
    intro i
    rw [hJcoord]
    have hs := b.sum_coord_apply_eq_one x
    simp only [Fin.sum_univ_three] at hs
    fin_cases i <;> simp [w, triangleComplexAffineMap_apply]
    linarith
  have hcoord (i : Fin 3) : ContDiff ℝ ∞ (b.coord i) := by
    rw [(b.coord i).decomp]
    exact (b.coord i).linear.toContinuousLinearMap.contDiff.add contDiff_const
  have hC : ContDiff ℝ ∞ (triangleComplexAffineMap b) :=
    Complex.equivRealProdCLM.symm.contDiff.comp
      (((hcoord 1).sub contDiff_const).prodMk ((hcoord 2).sub contDiff_const))
  have hJ : ContDiff ℝ ∞ J := by
    change ContDiff ℝ ∞ (fun z : ℂ => ∑ i : Fin 3, w z i • b i)
    simp only [Fin.sum_univ_three]
    change ContDiff ℝ ∞ (fun z : ℂ => (1 / 3 - z.re - z.im) • b 0 +
      (1 / 3 + z.re) • b 1 + (1 / 3 + z.im) • b 2)
    exact (((contDiff_const.sub Complex.reCLM.contDiff).sub
      Complex.imCLM.contDiff).smul contDiff_const).add
      (((contDiff_const.add Complex.reCLM.contDiff).smul contDiff_const)) |>.add
      ((contDiff_const.add Complex.imCLM.contDiff).smul contDiff_const)
  refine ⟨{
    toEquiv := {
      toFun := triangleComplexAffineMap b
      invFun := J
      left_inv := hJC
      right_inv := hCJ }
    contMDiff_toFun := hC.contMDiff
    contMDiff_invFun := hJ.contMDiff }, fun _ => rfl⟩

theorem triangleComplexAffineMap_roundedPolygon {n : ℕ} [NeZero n]
    (b : AffineBasis (Fin 3) ℝ E) (ρ : ℝ → ℝ) (p : Polygon E n) (t : ℝ) :
    triangleComplexAffineMap b (roundedPolygonParameter ρ p t) =
      roundedPolygonParameter ρ (⟨fun i => triangleComplexAffineMap b (p i)⟩ : Polygon ℂ n) t := by
  let C := triangleComplexAffineMap b
  have hformula (x y z : E) (a d : ℝ) :
      C (x + a • (x - y) + d • (z - x)) =
        C x + a • (C x - C y) + d • (C z - C x) := by
    rw [congrFun C.decomp (x + a • (x - y) + d • (z - x)),
      congrFun C.decomp x, congrFun C.decomp y, congrFun C.decomp z]
    simp only [Pi.add_apply, map_add, map_smul, map_sub]
    module
  exact hformula _ _ _ _ _

end PoincareConjecture.M25.Topology3D
