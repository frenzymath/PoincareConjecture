import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapGraph.Height
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapCollar

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

private theorem projection_norm_sq {v : E3} (hv : ‖v‖ = 1) (y : E3) :
    ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ ^ 2 =
      ‖y‖ ^ 2 - inner Real v y ^ 2 := by
  have hvv : inner Real v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  change ‖((Hemisphere.Plane v).orthogonalProjectionOnto y : E3)‖ ^ 2 = _
  rw [Submodule.coe_orthogonalProjectionOnto_apply, Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton Real hv, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    hvv, real_inner_comm y v, real_inner_self_eq_norm_sq]
  ring

private theorem boundedCapEquation_scale (z t k : Real) (hk : k ≠ 0)
    (hden : t ^ 2 + z ≠ 0) :
    boundedCapEquation (k ^ 2 * z) (k * t) = k ^ 2 * boundedCapEquation z t := by
  have harg : 4 * (k * t) ^ 2 / ((k * t) ^ 2 + k ^ 2 * z) =
      4 * t ^ 2 / (t ^ 2 + z) := by
    rw [show (k * t) ^ 2 + k ^ 2 * z = k ^ 2 * (t ^ 2 + z) by ring]
    field_simp
  unfold boundedCapEquation
  rw [harg]
  ring

private theorem source_equation {v : E3} (hv : ‖v‖ = 1) (p : S2) :
    boundedCylinderRadius v p ^ 2 *
      boundedCapEquation (‖(Hemisphere.Plane v).orthogonalProjectionOnto (p : E3)‖ ^ 2)
        (inner Real v (p : E3)) = 1 := by
  let u := inner Real v (p : E3)
  let z := ‖(Hemisphere.Plane v).orthogonalProjectionOnto (p : E3)‖ ^ 2
  have hz : z = 1 - u ^ 2 := by
    change ‖(Hemisphere.Plane v).orthogonalProjectionOnto (p : E3)‖ ^ 2 =
      1 - inner Real v (p : E3) ^ 2
    rw [projection_norm_sq hv]
    simp
  have hden : u ^ 2 + z = 1 := by rw [hz]; ring
  have hr : boundedCylinderRadius v p = (Real.sqrt (boundedCapEquation z u))⁻¹ := by
    unfold boundedCylinderRadius
    change (Real.sqrt ((1 - Real.smoothTransition (4 * u ^ 2 - 2)) * (1 - u ^ 2) +
      Real.smoothTransition (4 * u ^ 2 - 2) * u ^ 2))⁻¹ = _
    congr 2
    unfold boundedCapEquation
    rw [hden, div_one, hz]
    ring
  have hp : 0 < boundedCapEquation z u := by
    have := boundedCylinderRadius_pos v p
    rw [hr] at this
    exact Real.sqrt_pos.mp (inv_pos.mp this)
  change boundedCylinderRadius v p ^ 2 * boundedCapEquation z u = 1
  rw [hr, inv_pow, Real.sq_sqrt hp.le, inv_mul_cancel₀ hp.ne']

theorem boundedCapEquation_radial_point {v : E3} (hv : ‖v‖ = 1) (p : S2) :
    boundedCapEquation
      (‖(Hemisphere.Plane v).orthogonalProjectionOnto
        (boundedCylinderRadius v p • (p : E3))‖ ^ 2)
      (inner Real v (boundedCylinderRadius v p • (p : E3))) = 1 := by
  rw [map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (boundedCylinderRadius_pos v p), mul_pow, inner_smul_right,
    boundedCapEquation_scale _ _ _ (boundedCylinderRadius_pos v p).ne']
  · exact source_equation hv p
  · rw [projection_norm_sq hv]
    simp

theorem mem_boundedCylinderNorthernCap_iff_equation
    {v y : E3} (hv : ‖v‖ = 1) (hy : y ≠ 0) :
    y ∈ boundedCylinderNorthernCap v ↔
      0 ≤ inner Real v y ∧
        boundedCapEquation (‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ ^ 2)
          (inner Real v y) = 1 := by
  constructor
  · intro h
    refine ⟨height_nonneg_of_mem_boundedCylinderNorthernCap h, ?_⟩
    obtain ⟨p, hp, rfl⟩ := h
    exact boundedCapEquation_radial_point hv p
  · rintro ⟨ht, heq⟩
    let n := ‖y‖
    have hn : 0 < n := norm_pos_iff.mpr hy
    let p : S2 := ⟨n⁻¹ • y, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hn)]
      exact inv_mul_cancel₀ hn.ne'⟩
    have hp : n • (p : E3) = y := by
      change n • (n⁻¹ • y) = y
      rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hsource := source_equation hv p
    have hnorm : inner Real v (p : E3) ^ 2 +
        ‖(Hemisphere.Plane v).orthogonalProjectionOnto (p : E3)‖ ^ 2 ≠ 0 := by
      rw [projection_norm_sq hv]
      simp
    rw [← hp, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hn, mul_pow,
      inner_smul_right, boundedCapEquation_scale _ _ _ hn.ne' hnorm] at heq
    have hdne : boundedCapEquation
        (‖(Hemisphere.Plane v).orthogonalProjectionOnto (p : E3)‖ ^ 2)
        (inner Real v (p : E3)) ≠ 0 := by
      intro hd
      rw [hd, mul_zero] at hsource
      norm_num at hsource
    have hr : boundedCylinderRadius v p = n := by
      have hsq := mul_right_cancel₀ hdne (hsource.trans heq.symm)
      nlinarith [boundedCylinderRadius_pos v p]
    refine ⟨p, ?_, ?_⟩
    · change 0 ≤ inner Real v (n⁻¹ • y)
      rw [inner_smul_right]
      exact mul_nonneg (inv_nonneg.mpr hn.le) ht
    change boundedCylinderRadius v p • (p : E3) = y
    rw [hr]
    exact hp

theorem mem_boundedCylinderNorthernCap_iff_height
    {v y : E3} (hv : ‖v‖ = 1)
    (hy : ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ < 1) :
    y ∈ boundedCylinderNorthernCap v ↔
      inner Real v y =
        boundedCapHeight (‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ ^ 2) := by
  have hz : 0 ≤ ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ ^ 2 := sq_nonneg _
  have hz1 : ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ ^ 2 < 1 := by
    nlinarith [norm_nonneg ((Hemisphere.Plane v).orthogonalProjectionOnto y)]
  by_cases hy0 : y = 0
  · subst y
    have hnot : (0 : E3) ∉ boundedCylinderNorthernCap v := by
      rintro ⟨p, hp, heq⟩
      have := congrArg norm heq
      simp [norm_smul, abs_of_pos (boundedCylinderRadius_pos v p),
        (boundedCylinderRadius_pos v p).ne'] at this
    simp [hnot, boundedCapHeight_eq_one (by norm_num : (0 : Real) ≤ 1 / 3)]
  rw [mem_boundedCylinderNorthernCap_iff_equation hv hy0]
  constructor
  · rintro ⟨ht, heq⟩
    exact (boundedCapHeight_eq_of_equation hz hz1 ht heq).symm
  · intro heq
    rw [heq]
    exact boundedCapHeight_spec hz hz1

theorem mem_boundedCylinderNorthernCap_iff_boundary_height
    {v y : E3} (hv : ‖v‖ = 1)
    (hy : ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ = 1) :
    y ∈ boundedCylinderNorthernCap v ↔ inner Real v y ∈ Icc (0 : Real) 1 := by
  have hy0 : y ≠ 0 := by intro h; simp [h] at hy
  rw [mem_boundedCylinderNorthernCap_iff_equation hv hy0, hy, one_pow]
  constructor
  · rintro ⟨ht, heq⟩
    refine ⟨ht, ?_⟩
    by_contra hn
    have ht1 : 1 < inner Real v y := lt_of_not_ge hn
    have ht2 : 1 < inner Real v y ^ 2 := by nlinarith
    have hd : 0 < inner Real v y ^ 2 + 1 := by positivity
    have ha : 0 < 4 * inner Real v y ^ 2 / (inner Real v y ^ 2 + 1) - 2 := by
      apply sub_pos.mpr
      apply (lt_div_iff₀ hd).mpr
      nlinarith
    have hp := mul_pos (Real.smoothTransition.pos_of_pos ha) (sub_pos.mpr ht2)
    unfold boundedCapEquation at heq
    linarith
  · rintro ⟨ht, ht1⟩
    refine ⟨ht, ?_⟩
    have hd : 0 < inner Real v y ^ 2 + 1 := by positivity
    have ha : 4 * inner Real v y ^ 2 / (inner Real v y ^ 2 + 1) - 2 ≤ 0 := by
      apply sub_nonpos.mpr
      apply (div_le_iff₀ hd).mpr
      nlinarith
    simp [boundedCapEquation, Real.smoothTransition.zero_of_nonpos ha]

theorem mem_boundedCylinderNorthernCap_iff_cases
    {v y : E3} (hv : ‖v‖ = 1) :
    y ∈ boundedCylinderNorthernCap v ↔
      (‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ = 1 ∧
        inner Real v y ∈ Icc (0 : Real) 1) ∨
      (‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ < 1 ∧
        inner Real v y = boundedCapHeight
          (‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ ^ 2)) := by
  constructor
  · intro hy
    have hn : ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ ≤ 1 := by
      obtain ⟨p, hp, rfl⟩ := hy
      exact norm_boundedCylinder_projection_le v hv p
    rcases hn.eq_or_lt with heq | hlt
    · exact Or.inl ⟨heq, (mem_boundedCylinderNorthernCap_iff_boundary_height hv heq).mp hy⟩
    · exact Or.inr ⟨hlt, (mem_boundedCylinderNorthernCap_iff_height hv hlt).mp hy⟩
  · rintro (⟨hn, ht⟩ | ⟨hn, ht⟩)
    · exact (mem_boundedCylinderNorthernCap_iff_boundary_height hv hn).mpr ht
    · exact (mem_boundedCylinderNorthernCap_iff_height hv hn).mpr ht

end Poincare.Manifold.Schoenflies
