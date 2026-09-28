import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.TwoCaps



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1


theorem one_le_boundedCylinderRadius (v : E3) (hv : ‖v‖ = 1) (p : S2) :
    1 ≤ boundedCylinderRadius v p := by
  let h := inner Real v (p : E3)
  let a := Real.smoothTransition (4 * h ^ 2 - 2)
  have hh : h ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one h).mpr (by
    simpa [h, hv] using abs_real_inner_le_norm v (p : E3))
  have ha0 : 0 ≤ a := Real.smoothTransition.nonneg _
  have ha1 : a ≤ 1 := Real.smoothTransition.le_one _
  have hd : (1 - a) * (1 - h ^ 2) + a * h ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha1) (sq_nonneg h),
      mul_nonneg ha0 (sub_nonneg.mpr hh)]
  have hspos : 0 < Real.sqrt ((1 - a) * (1 - h ^ 2) + a * h ^ 2) := by
    have := boundedCylinderRadius_pos v p
    change 0 < (Real.sqrt ((1 - a) * (1 - h ^ 2) + a * h ^ 2))⁻¹ at this
    exact inv_pos.mp this
  have hsle : Real.sqrt ((1 - a) * (1 - h ^ 2) + a * h ^ 2) ≤ 1 := by
    have hnonneg := Real.sqrt_pos.mp hspos
    nlinarith [Real.sq_sqrt hnonneg.le]
  change 1 ≤ (Real.sqrt ((1 - a) * (1 - h ^ 2) + a * h ^ 2))⁻¹
  rw [← one_div, le_div_iff₀ hspos]
  simpa using hsle

private theorem norm_projection_sq (v : E3) (hv : ‖v‖ = 1) (p : S2) :
    ‖(Hemisphere.Plane v).orthogonalProjectionOnto (p : E3)‖ ^ 2 =
      1 - inner Real v (p : E3) ^ 2 := by
  have hvv : inner Real v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hpp : inner Real (p : E3) p = 1 := by simp
  change ‖((Hemisphere.Plane v).orthogonalProjectionOnto (p : E3) : E3)‖ ^ 2 = _
  rw [Submodule.coe_orthogonalProjectionOnto_apply, Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton Real hv, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    hvv, hpp, real_inner_comm (p : E3) v]
  ring

theorem norm_boundedCylinder_projection_eq_one_of_source_belt
    (v : E3) (hv : ‖v‖ = 1) (p : S2)
    (hp : |inner Real v (p : E3)| ≤ 1 / 2) :
    ‖(Hemisphere.Plane v).orthogonalProjectionOnto
      (boundedCylinderRadius v p • (p : E3))‖ = 1 := by
  have hsq : inner Real v (p : E3) ^ 2 ≤ 1 / 4 := by
    nlinarith [sq_abs (inner Real v (p : E3)),
      (sq_le_sq₀ (abs_nonneg (inner Real v (p : E3)))
        (by norm_num : (0 : Real) ≤ 1 / 2)).mpr hp]
  have hpos : 0 < 1 - inner Real v (p : E3) ^ 2 := by linarith
  have hn : ‖(Hemisphere.Plane v).orthogonalProjectionOnto (p : E3)‖ =
      Real.sqrt (1 - inner Real v (p : E3) ^ 2) := by
    rw [← norm_projection_sq v hv p, Real.sqrt_sq (norm_nonneg _)]
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (boundedCylinderRadius_pos v p),
    boundedCylinderRadius_of_abs_height_le v p hp, hn]
  exact inv_mul_cancel₀ (Real.sqrt_pos.mpr hpos).ne'



theorem norm_boundedCylinder_projection_eq_one_of_height_belt
    (v : E3) (hv : ‖v‖ = 1) (p : S2)
    (hp : |inner Real v (boundedCylinderRadius v p • (p : E3))| ≤ 1 / 4) :
    ‖(Hemisphere.Plane v).orthogonalProjectionOnto
      (boundedCylinderRadius v p • (p : E3))‖ = 1 := by
  apply norm_boundedCylinder_projection_eq_one_of_source_belt v hv p
  rw [inner_smul_right, abs_mul, abs_of_pos (boundedCylinderRadius_pos v p)] at hp
  nlinarith [one_le_boundedCylinderRadius v hv p,
    abs_nonneg (inner Real v (p : E3))]



theorem mem_boundedCylinder_sphere_iff_of_height_belt
    (v : E3) (hv : ‖v‖ = 1) (y : E3)
    (hy : |inner Real v y| ≤ 1 / 4) :
    y ∈ range (fun p : S2 => boundedCylinderRadius v p • (p : E3)) ↔
      ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ = 1 := by
  constructor
  · rintro ⟨p, rfl⟩
    exact norm_boundedCylinder_projection_eq_one_of_height_belt v hv p hy
  · intro hproj
    have hnorm : 1 ≤ ‖y‖ := by
      rw [← hproj]
      exact (Hemisphere.Plane v).norm_orthogonalProjectionOnto_apply_le y
    have hypos : 0 < ‖y‖ := by linarith
    let p : S2 := ⟨‖y‖⁻¹ • y, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hypos), inv_mul_cancel₀ hypos.ne']⟩
    have hinv : ‖y‖⁻¹ ≤ 1 := by
      rw [← one_div, div_le_iff₀ hypos]
      simpa using hnorm
    have hp : |inner Real v (p : E3)| ≤ 1 / 2 := by
      change |inner Real v (‖y‖⁻¹ • y)| ≤ 1 / 2
      rw [inner_smul_right, abs_mul, abs_of_pos (inv_pos.mpr hypos)]
      nlinarith [abs_nonneg (inner Real v y)]
    have hb := norm_boundedCylinder_projection_eq_one_of_source_belt v hv p hp
    have heq : boundedCylinderRadius v p * ‖y‖⁻¹ = 1 := by
      change ‖(Hemisphere.Plane v).orthogonalProjectionOnto
        (boundedCylinderRadius v p • (‖y‖⁻¹ • y))‖ = 1 at hb
      simpa only [map_smul, norm_smul, Real.norm_eq_abs,
        abs_of_pos (boundedCylinderRadius_pos v p), abs_of_pos (inv_pos.mpr hypos),
        hproj, mul_one] using hb
    refine ⟨p, ?_⟩
    change boundedCylinderRadius v p • (‖y‖⁻¹ • y) = y
    rw [smul_smul, heq, one_smul]


theorem reflection_mem_boundedCylinder_sphere_iff (v : E3) (y : E3) :
    (Hemisphere.Plane v).reflection y ∈
        range (fun p : S2 => boundedCylinderRadius v p • (p : E3)) ↔
      y ∈ range (fun p : S2 => boundedCylinderRadius v p • (p : E3)) := by
  let R := (Hemisphere.Plane v).reflection
  have hforward (x : E3)
      (hx : x ∈ range (fun p : S2 => boundedCylinderRadius v p • (p : E3))) :
      R x ∈ range (fun p : S2 => boundedCylinderRadius v p • (p : E3)) := by
    obtain ⟨p, rfl⟩ := hx
    let q : S2 := ⟨R p, by rw [mem_sphere_zero_iff_norm, R.norm_map, norm_eq_of_mem_sphere]⟩
    have hinner : inner Real v (q : E3) = -inner Real v (p : E3) := by
      have h := R.inner_map_map v (p : E3)
      rw [Submodule.reflection_orthogonalComplement_singleton_eq_neg, inner_neg_left] at h
      change inner Real v (R (p : E3)) = -inner Real v (p : E3)
      linarith
    have hr : boundedCylinderRadius v q = boundedCylinderRadius v p :=
      boundedCylinderRadius_eq_of_sq_height_eq v (by rw [hinner, neg_sq])
    refine ⟨q, ?_⟩
    change boundedCylinderRadius v q • R (p : E3) = R (boundedCylinderRadius v p • p)
    rw [hr, map_smul]
  constructor
  · intro hy
    simpa only [R, Submodule.reflection_reflection] using hforward (R y) hy
  · exact hforward y

end Poincare.Manifold.Schoenflies
