import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Homeomorph.Defs










set_option autoImplicit false

open Set

namespace AffineMap




theorem exists_zero_level_affineSubspace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ell : E →ᵃ[ℝ] ℝ) (hell : ell.linear ≠ 0) :
    ∃ A : AffineSubspace ℝ E,
      (A : Set E) = {x | ell x = 0} ∧ A.direction = ell.linear.ker := by
  obtain ⟨p, hp⟩ := (ell.linear_surjective_iff.mp (LinearMap.surjective hell)) 0
  refine ⟨AffineSubspace.mk' p ell.linear.ker, ?_, AffineSubspace.direction_mk' _ _⟩
  ext x
  change ell.linear (x - p) = 0 ↔ ell x = 0
  have hval : ell.linear (x - p) = ell x - ell p := ell.linearMap_vsub x p
  rw [hval, hp, sub_zero]

end AffineMap

namespace Homeomorph



theorem affine_height_eq_of_displacement_mem_ker
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E ≃ₜ E) (ell : E →ᵃ[ℝ] ℝ)
    (hdir : ∀ x, H x - x ∈ ell.linear.ker) (x : E) :
    ell (H x) = ell x := by
  have hz : ell.linear (H x - x) = 0 := hdir x
  have heq : ell.linear (H x - x) = ell (H x) - ell x :=
    ell.linearMap_vsub (H x) x
  exact sub_eq_zero.mp (heq.symm.trans hz)




theorem affine_height_preimages_of_displacement_mem_ker
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E ≃ₜ E) (ell : E →ᵃ[ℝ] ℝ)
    (hdir : ∀ x, H x - x ∈ ell.linear.ker) (S : Set ℝ) :
    H ⁻¹' (ell ⁻¹' S) = ell ⁻¹' S ∧
      H.symm ⁻¹' (ell ⁻¹' S) = ell ⁻¹' S := by
  have hheight := H.affine_height_eq_of_displacement_mem_ker ell hdir
  constructor
  · ext x
    change ell (H x) ∈ S ↔ ell x ∈ S
    rw [hheight x]
  · ext x
    change ell (H.symm x) ∈ S ↔ ell x ∈ S
    have h := hheight (H.symm x)
    rw [H.apply_symm_apply] at h
    rw [h]

end Homeomorph
