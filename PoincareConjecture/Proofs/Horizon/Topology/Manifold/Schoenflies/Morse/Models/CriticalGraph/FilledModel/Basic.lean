import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.Radial.Ambient
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.Radial.Equation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.ProfileGeometry
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapCollar

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

def quadraticMinimumLowerSurface (v : E3) : Set E3 :=
  {y | inner Real v y ∈ Icc (-2 : Real) 0 ∧
    ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ ^ 2 =
      minimumCapSquaredRadius (inner Real v y + 2)}

private theorem projection_sq {v : E3} (hv : ‖v‖ = 1) (y : E3) :
    ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ ^ 2 = ‖y‖ ^ 2 - inner Real v y ^ 2 := by
  have hvv : inner Real v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  change ‖((Hemisphere.Plane v).orthogonalProjectionOnto y : E3)‖ ^ 2 = _
  rw [Submodule.coe_orthogonalProjectionOnto_apply, Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton Real hv, ← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    hvv, real_inner_comm y v, real_inner_self_eq_norm_sq]
  ring

private theorem radius_eq_lower {v : E3} (p : S2) (hp : inner Real v (p : E3) ≤ 0) :
    quadraticMinimumRadius v p = minimumCapLowerRadius (inner Real v (p : E3)) := by
  by_cases hn : inner Real v (p : E3) < 0
  · exact if_pos hn
  · have he : inner Real v (p : E3) = 0 := le_antisymm hp (le_of_not_gt hn)
    rw [quadraticMinimumRadius_eq_north p (by linarith),
      boundedCylinderRadius_of_abs_height_le v p (by rw [he]; norm_num), he]
    norm_num [minimumCapLowerRadius]

theorem image_quadraticMinimum_south_eq_lower {v : E3} (hv : ‖v‖ = 1) :
    (fun p : S2 => quadraticMinimumRadius v p • (p : E3)) ''
      {p | inner Real v (p : E3) ≤ 0} = quadraticMinimumLowerSurface v := by
  apply Subset.antisymm
  · rintro y ⟨p, hp, rfl⟩
    have ht : inner Real v (p : E3) ∈ Icc (-1 : Real) 0 := by
      have hh : |inner Real v (p : E3)| ≤ 1 := by
        simpa [hv] using abs_real_inner_le_norm v (p : E3)
      exact ⟨(abs_le.mp hh).1, hp⟩
    have he := minimumCapLowerRadius_equation ht
    change _ ∈ Icc (-2 : Real) 0 ∧ _ = _
    rw [inner_smul_right, radius_eq_lower p hp]
    refine ⟨he.1, ?_⟩
    rw [map_smul, norm_smul, Real.norm_eq_abs, radius_eq_lower p hp,
      abs_of_pos (minimumCapLowerRadius_pos ht), mul_pow, projection_sq hv]
    simpa only [norm_eq_of_mem_sphere, one_pow] using he.2
  · intro y hy
    obtain ⟨hyh, hyp⟩ := hy
    have hyne : y ≠ 0 := by
      intro he
      subst y
      simp only [map_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, inner_zero_right, zero_add] at hyp
      rw [minimumCapSquaredRadius_eq_one (by norm_num)] at hyp
      norm_num at hyp
    have hn : 0 < ‖y‖ := norm_pos_iff.mpr hyne
    let p : S2 := ⟨‖y‖⁻¹ • y, by
      rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']⟩
    have hph : inner Real v (p : E3) = inner Real v y / ‖y‖ := by
      change inner Real v (‖y‖⁻¹ • y) = _
      rw [inner_smul_right]
      ring
    have ht : inner Real v (p : E3) ∈ Icc (-1 : Real) 0 := by
      have hh : |inner Real v (p : E3)| ≤ 1 := by
        simpa [hv] using abs_real_inner_le_norm v (p : E3)
      exact ⟨(abs_le.mp hh).1, by rw [hph]; exact div_nonpos_of_nonpos_of_nonneg hyh.2 hn.le⟩
    have he := minimumCapLowerRadius_eq_of_equation ht
      (show inner Real v y + 2 ∈ Icc (0 : Real) 2 by constructor <;> linarith [hyh.1, hyh.2]) hn
      (show ‖y‖ * inner Real v (p : E3) = inner Real v y + 2 - 2 by
        rw [hph]; field_simp; ring)
      (show ‖y‖ ^ 2 * (1 - inner Real v (p : E3) ^ 2) =
        minimumCapSquaredRadius (inner Real v y + 2) by
          rw [hph, ← hyp, projection_sq hv]
          field_simp)
    refine ⟨p, ht.2, ?_⟩
    dsimp only
    rw [radius_eq_lower p ht.2, he]
    change ‖y‖ • (‖y‖⁻¹ • y) = y
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]

theorem range_quadraticMinimum_radial {v : E3} (hv : ‖v‖ = 1) :
    range (fun p : S2 => quadraticMinimumRadius v p • (p : E3)) =
      quadraticMinimumLowerSurface v ∪ boundedCylinderNorthernCap v := by
  rw [← image_quadraticMinimum_south_eq_lower hv]
  apply Subset.antisymm
  · rintro y ⟨p, rfl⟩
    by_cases hp : 0 ≤ inner Real v (p : E3)
    · right
      exact ⟨p, hp, by dsimp only; rw [quadraticMinimumRadius_eq_north p hp]⟩
    · exact Or.inl ⟨p, (lt_of_not_ge hp).le, rfl⟩
  · rintro y (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
    · exact ⟨p, rfl⟩
    · exact ⟨p, by dsimp only; rw [quadraticMinimumRadius_eq_north p hp]⟩

theorem quadraticMinimumLowerSurface_eq_cap_union_cylinder {v : E3} (hv : ‖v‖ = 1) :
    quadraticMinimumLowerSurface v = quadraticMinimumCap v (-2) 1 ∪
      (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
        (Icc (-2 + (7 / 8 : Real) ^ 2) 0 ×ˢ sphere (0 : Hemisphere.Plane v) 1) := by
  have hcylinder (y : E3) :
      y ∈ (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
        (Icc (-2 + (7 / 8 : Real) ^ 2) 0 ×ˢ sphere (0 : Hemisphere.Plane v) 1) ↔
      inner Real v y ∈ Icc (-2 + (7 / 8 : Real) ^ 2) 0 ∧
        ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ = 1 := by
    constructor
    · rintro ⟨⟨t, q⟩, ⟨ht, hq⟩, rfl⟩
      have he := (Poincare.Geometry.Euclidean.heightCoordinates hv).symm_apply_apply (t, q)
      exact ⟨by rw [show inner Real v (t • v + (q : E3)) = t from congrArg Prod.fst he]; exact ht,
        by rw [show (Hemisphere.Plane v).orthogonalProjectionOnto (t • v + (q : E3)) = q from
          congrArg Prod.snd he]; exact mem_sphere_zero_iff_norm.mp hq⟩
    · rintro ⟨hh, hq⟩
      exact ⟨(inner Real v y, (Hemisphere.Plane v).orthogonalProjectionOnto y),
        ⟨hh, mem_sphere_zero_iff_norm.mpr hq⟩,
        (Poincare.Geometry.Euclidean.heightCoordinates hv).apply_symm_apply y⟩
  ext y
  rw [mem_union, mem_quadraticMinimumCap_iff hv (-2) (by norm_num : (0 : Real) < 1), hcylinder]
  simp only [one_pow, one_mul, mul_one, div_one]
  change (inner Real v y ∈ Icc (-2 : Real) 0 ∧
    ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ ^ 2 =
      minimumCapSquaredRadius (inner Real v y + 2)) ↔ _
  constructor
  · rintro ⟨hh, hq⟩
    by_cases hu : inner Real v y + 2 < 1 / 2
    · have hR := strictMonoOn_minimumCapSquaredRadius
        (show inner Real v y + 2 ∈ Icc (0 : Real) (1 / 2) from ⟨by linarith [hh.1], hu.le⟩)
        (show (1 / 2 : Real) ∈ Icc (0 : Real) (1 / 2) by norm_num) hu
      rw [minimumCapSquaredRadius_eq_one le_rfl, ← hq] at hR
      have hH := minimumCapHeight_eq_of_radius
        (sq_nonneg ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖) hR
        ⟨by linarith [hh.1], hu⟩ hq.symm
      exact Or.inl (Or.inl ⟨by nlinarith [norm_nonneg ((Hemisphere.Plane v).orthogonalProjectionOnto y)],
        by rw [hH]; ring⟩)
    · rw [minimumCapSquaredRadius_eq_one (le_of_not_gt hu)] at hq
      have hn : ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ = 1 := by
        nlinarith [norm_nonneg ((Hemisphere.Plane v).orthogonalProjectionOnto y)]
      by_cases hb : inner Real v y ≤ -2 + (7 / 8 : Real) ^ 2
      · exact Or.inl (Or.inr ⟨hn, by constructor <;> linarith⟩)
      · exact Or.inr ⟨⟨(lt_of_not_ge hb).le, hh.2⟩, hn⟩
  · rintro ((⟨hq, hh⟩ | ⟨hq, hh⟩) | ⟨hh, hq⟩)
    · have hq1 : ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ ^ 2 < 1 := by
        nlinarith [norm_nonneg ((Hemisphere.Plane v).orthogonalProjectionOnto y)]
      obtain ⟨hu, he⟩ := minimumCapHeight_spec
        (sq_nonneg ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖) hq1
      rw [hh]
      refine ⟨⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
      convert he.symm using 1
      congr 1
      ring
    · refine ⟨⟨by linarith [hh.1], by norm_num at hh; linarith [hh.2]⟩, ?_⟩
      rw [hq, one_pow, minimumCapSquaredRadius_eq_one (by linarith [hh.1])]
    · refine ⟨⟨by norm_num at hh; linarith [hh.1], hh.2⟩, ?_⟩
      rw [hq, one_pow, minimumCapSquaredRadius_eq_one (by norm_num at hh; linarith [hh.1])]

theorem exists_ambient_quadraticMinimum_model {v : E3} (hv : ‖v‖ = 1) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∃ K : Set E3, IsCompact K ∧ ∀ y ∉ K, F y = y) ∧
      F '' sphere (0 : E3) 1 =
        quadraticMinimumCap v (-2) 1 ∪
          (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
            (Icc (-2 + (7 / 8 : Real) ^ 2) 0 ×ˢ sphere (0 : Hemisphere.Plane v) 1) ∪
          boundedCylinderNorthernCap v := by
  obtain ⟨F, hsupport, hF, _, _⟩ := exists_quadraticMinimum_radial_ambient hv
  refine ⟨F, hsupport, ?_⟩
  have hrange : F '' sphere (0 : E3) 1 =
      range (fun p : S2 => quadraticMinimumRadius v p • (p : E3)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, (hF ⟨x, hx⟩).symm⟩
    · rintro ⟨p, rfl⟩
      exact ⟨p, p.property, hF p⟩
  rw [hrange, range_quadraticMinimum_radial hv,
    quadraticMinimumLowerSurface_eq_cap_union_cylinder hv]

end Poincare.Manifold.Schoenflies
