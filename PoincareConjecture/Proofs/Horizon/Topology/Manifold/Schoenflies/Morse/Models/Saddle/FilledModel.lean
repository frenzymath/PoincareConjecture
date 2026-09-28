import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.UpperCap

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

def band : Set E3 := {p | polynomial p = 1 ∧ p 2 ∈ Icc (-9/8) (1/2)}

theorem shear_image_sphere_eq_band_union_caps :
    shear '' sphere (0 : E3) 1 =
      band ∪ (lowerCap 1 '' closedBall (0 : E2) (Real.sqrt (1/8))) ∪
        (lowerCap (-1) '' closedBall (0 : E2) (Real.sqrt (1/8))) ∪
        (upperCap '' closedBall (0 : E2) (Real.sqrt (3/4))) := by
  rw [shear_image_sphere, lowerCap_image_closedBall (by norm_num : (1 : Real)^2 = 1),
    lowerCap_image_closedBall (by norm_num : (-1 : Real)^2 = 1), upperCap_image_closedBall]
  ext p
  constructor
  · intro hp
    by_cases hl : p 2 ≤ -9/8
    · by_cases hx : 0 ≤ p 0
      · exact Or.inl (Or.inl (Or.inr ⟨hp, hl, by simpa using hx⟩))
      · exact Or.inl (Or.inr ⟨hp, hl, by dsimp; linarith⟩)
    · by_cases hu : 1/2 ≤ p 2
      · exact Or.inr ⟨hp, hu⟩
      · exact Or.inl (Or.inl (Or.inl ⟨hp, le_of_lt (lt_of_not_ge hl),
          le_of_lt (lt_of_not_ge hu)⟩))
  · rintro (((hp | hp) | hp) | hp) <;> exact hp.1

theorem band_inter_lowerCap {σ : Real} (hσ : σ^2 = 1) :
    band ∩ (lowerCap σ '' closedBall (0 : E2) (Real.sqrt (1/8))) =
      lowerCap σ '' sphere (0 : E2) (Real.sqrt (1/8)) := by
  apply Subset.antisymm
  · rintro p ⟨hp, ⟨q, hq, rfl⟩⟩
    refine ⟨q, ?_, rfl⟩
    have hcap := (lowerCap_image_closedBall hσ) ▸ mem_image_of_mem (lowerCap σ) hq
    have hh : lowerCap σ q 2 = -9/8 := le_antisymm hcap.2.1 hp.2.1
    rw [lowerCap_height] at hh
    rw [mem_sphere_zero_iff_norm]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 1/8),
      Real.sqrt_nonneg (1/8), norm_nonneg q]
  · rintro p ⟨q, hq, rfl⟩
    refine ⟨⟨lowerCap_mem_surface hσ
      (lower_closedBall_subset_domain (sphere_subset_closedBall hq)), ?_⟩,
      mem_image_of_mem (lowerCap σ) (sphere_subset_closedBall hq)⟩
    rw [lowerCap_boundary_height σ hq]
    norm_num

theorem band_inter_upperCap :
    band ∩ (upperCap '' closedBall (0 : E2) (Real.sqrt (3/4))) =
      upperCap '' sphere (0 : E2) (Real.sqrt (3/4)) := by
  apply Subset.antisymm
  · rintro p ⟨hp, ⟨q, hq, rfl⟩⟩
    refine ⟨q, ?_, rfl⟩
    have hcap := upperCap_image_closedBall ▸ mem_image_of_mem upperCap hq
    have hh : upperCap q 2 = 1/2 := le_antisymm hp.2.2 hcap.2
    have hn := (upperCap_height_eq_iff (upper_closedBall_subset_domain hq)).mp hh
    rw [mem_sphere_zero_iff_norm]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 3/4),
      Real.sqrt_nonneg (3/4), norm_nonneg q]
  · rintro p ⟨q, hq, rfl⟩
    refine ⟨⟨upperCap_mem_surface
      (upper_closedBall_subset_domain (sphere_subset_closedBall hq)), ?_⟩,
      mem_image_of_mem upperCap (sphere_subset_closedBall hq)⟩
    rw [upperCap_boundary_height hq]
    norm_num

theorem lowerCap_disjoint_upperCap {σ : Real} (hσ : σ^2 = 1) :
    Disjoint (lowerCap σ '' closedBall (0 : E2) (Real.sqrt (1/8)))
      (upperCap '' closedBall (0 : E2) (Real.sqrt (3/4))) := by
  rw [lowerCap_image_closedBall hσ, upperCap_image_closedBall]
  apply disjoint_left.mpr
  intro p hp hq
  linarith [hp.2.1, hq.2]

private theorem image_openBall_eq_sdiff_boundary
    (g : E2 → E3) (r : Real) (hgi : InjOn g (closedBall 0 r)) :
    g '' ball (0 : E2) r = (g '' closedBall (0 : E2) r) \ (g '' sphere (0 : E2) r) := by
  apply Subset.antisymm
  · rintro p ⟨q, hq, rfl⟩
    refine ⟨mem_image_of_mem g (ball_subset_closedBall hq), ?_⟩
    rintro ⟨z, hz, hzq⟩
    have heq := hgi (sphere_subset_closedBall hz) (ball_subset_closedBall hq) hzq
    rw [heq] at hz
    exact (ne_of_lt (mem_ball_zero_iff.mp hq)) (mem_sphere_zero_iff_norm.mp hz)
  · rintro p ⟨⟨q, hq, rfl⟩, hnot⟩
    refine ⟨q, ?_, rfl⟩
    rw [mem_ball_zero_iff]
    apply lt_of_le_of_ne (mem_closedBall_zero_iff.mp hq)
    intro heq
    exact hnot (mem_image_of_mem g (mem_sphere_zero_iff_norm.mpr heq))

theorem band_eq_sphere_minus_open_caps :
    band = (shear '' sphere (0 : E3) 1) \
      ((lowerCap 1 '' ball (0 : E2) (Real.sqrt (1/8))) ∪
        (lowerCap (-1) '' ball (0 : E2) (Real.sqrt (1/8))) ∪
        (upperCap '' ball (0 : E2) (Real.sqrt (3/4)))) := by
  rw [image_openBall_eq_sdiff_boundary (lowerCap 1) _
      ((lowerCap_injOn (by norm_num : (1 : Real)^2=1)).mono lower_closedBall_subset_domain),
    image_openBall_eq_sdiff_boundary (lowerCap (-1)) _
      ((lowerCap_injOn (by norm_num : (-1 : Real)^2=1)).mono lower_closedBall_subset_domain),
    image_openBall_eq_sdiff_boundary upperCap _ upperCap_injective.injOn,
    ← band_inter_lowerCap (by norm_num : (1 : Real)^2=1),
    ← band_inter_lowerCap (by norm_num : (-1 : Real)^2=1),
    ← band_inter_upperCap, shear_image_sphere_eq_band_union_caps]
  ext p
  simp only [mem_sdiff, mem_union, mem_inter_iff]
  tauto

theorem exists_ambient_filled_three_cap_model :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      F '' closedBall (0 : E3) 1 = {p | polynomial p ≤ 1} ∧
      F '' ball (0 : E3) 1 = {p | polynomial p < 1} ∧
      F '' sphere (0 : E3) 1 =
        band ∪ (lowerCap 1 '' closedBall (0 : E2) (Real.sqrt (1/8))) ∪
          (lowerCap (-1) '' closedBall (0 : E2) (Real.sqrt (1/8))) ∪
          (upperCap '' closedBall (0 : E2) (Real.sqrt (3/4))) :=
  ⟨shear, shear_image_closedBall, shear_image_ball, shear_image_sphere_eq_band_union_caps⟩

end Poincare.Manifold.Schoenflies.Saddle
