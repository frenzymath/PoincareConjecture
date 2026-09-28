import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapGraph.Representation



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Euclidean

private abbrev E3 := EuclideanSpace Real (Fin 3)



theorem mem_boundedCylinderNorthernCap_iff_of_height_lt_one
    {v y : E3} (hv : ‖v‖ = 1) (hy : inner Real v y < 1) :
    y ∈ boundedCylinderNorthernCap v ↔
      0 ≤ inner Real v y ∧ ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ = 1 := by
  rw [mem_boundedCylinderNorthernCap_iff_cases hv]
  constructor
  · rintro (⟨hn, ht⟩ | ⟨hn, ht⟩)
    · exact ⟨ht.1, hn⟩
    · have hsq : ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ ^ 2 < 1 := by
        nlinarith [norm_nonneg ((Hemisphere.Plane v).orthogonalProjectionOnto y)]
      have hheight := one_le_boundedCapHeight
        (sq_nonneg ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖) hsq
      rw [← ht] at hheight
      linarith
  · rintro ⟨ht, hn⟩
    exact Or.inl ⟨hn, ht, hy.le⟩



theorem lifted_cap_slice_eq_circle
    {v : E3} (hv : ‖v‖ = 1) (c s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    {t : Real} (ht : t ∈ Ico (0 : Real) 1) :
    (liftPlaneDiffeomorph hv c s hs A '' boundedCylinderNorthernCap v) ∩
      {y : E3 | inner Real v y = c + s * t} =
        (fun x : Hemisphere.Plane v => (c + s * t) • v + (A x : E3)) ''
          sphere (0 : Hemisphere.Plane v) 1 := by
  let L := liftPlaneDiffeomorph hv c s hs A
  ext y
  constructor
  · rintro ⟨⟨z, hz, rfl⟩, hh⟩
    have hzt : inner Real v z = t := by
      change inner Real v (liftPlaneDiffeomorph hv c s hs A z) = c + s * t at hh
      rw [inner_liftPlaneDiffeomorph] at hh
      exact mul_left_cancel₀ hs (add_left_cancel hh)
    have hp := (mem_boundedCylinderNorthernCap_iff_of_height_lt_one hv
      (by rw [hzt]; exact ht.2)).mp hz
    refine ⟨(Hemisphere.Plane v).orthogonalProjectionOnto z,
      mem_sphere_zero_iff_norm.mpr hp.2, ?_⟩
    rw [liftPlaneDiffeomorph_apply, hzt]
  · rintro ⟨x, hx, rfl⟩
    let z := heightCoordinates hv (t, x)
    have hzh : inner Real v z = t := inner_heightCoordinates hv (t, x)
    have hzp : (Hemisphere.Plane v).orthogonalProjectionOnto z = x :=
      congrArg Prod.snd ((heightCoordinates hv).symm_apply_apply (t, x))
    have hz : z ∈ boundedCylinderNorthernCap v :=
      (mem_boundedCylinderNorthernCap_iff_of_height_lt_one hv
        (by rw [hzh]; exact ht.2)).mpr ⟨by rw [hzh]; exact ht.1,
        by rw [hzp]; exact mem_sphere_zero_iff_norm.mp hx⟩
    have hLz : L z = (c + s * t) • v + (A x : E3) := by
      change liftPlaneDiffeomorph hv c s hs A z = _
      rw [liftPlaneDiffeomorph_apply, hzh, hzp]
    refine ⟨⟨z, hz, hLz⟩, ?_⟩
    change inner Real v ((c + s * t) • v + (A x : E3)) = c + s * t
    rw [← hLz]
    exact (inner_liftPlaneDiffeomorph hv c s hs A z).trans (by rw [hzh])



theorem lifted_cap_closed_strip_eq_cylinder
    {v : E3} (hv : ‖v‖ = 1) (c s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    {l u : Real} (hl : 0 ≤ l) (hu : u < 1) :
    (liftPlaneDiffeomorph hv c s hs A '' boundedCylinderNorthernCap v) ∩
      {y : E3 | (inner Real v y - c) / s ∈ Icc l u} =
        (fun z : Real × Hemisphere.Plane v => (c + s * z.1) • v + (A z.2 : E3)) ''
          (Icc l u ×ˢ sphere (0 : Hemisphere.Plane v) 1) := by
  ext y
  constructor
  · rintro ⟨hy, ht⟩
    let t := (inner Real v y - c) / s
    have ht01 : t ∈ Ico (0 : Real) 1 := ⟨hl.trans ht.1, ht.2.trans_lt hu⟩
    have hh : inner Real v y = c + s * t := by dsimp [t]; field_simp; ring
    have hm : y ∈ (fun x : Hemisphere.Plane v => (c + s * t) • v + (A x : E3)) ''
        sphere (0 : Hemisphere.Plane v) 1 := by
      rw [← lifted_cap_slice_eq_circle hv c s hs A ht01]
      exact ⟨hy, hh⟩
    obtain ⟨x, hx, hxy⟩ := hm
    exact ⟨(t, x), ⟨ht, hx⟩, hxy⟩
  · rintro ⟨⟨t, x⟩, ⟨ht, hx⟩, rfl⟩
    have hm : (c + s * t) • v + (A x : E3) ∈
        (liftPlaneDiffeomorph hv c s hs A '' boundedCylinderNorthernCap v) ∩
          {y : E3 | inner Real v y = c + s * t} := by
      rw [lifted_cap_slice_eq_circle hv c s hs A ⟨hl.trans ht.1, ht.2.trans_lt hu⟩]
      exact ⟨x, hx, rfl⟩
    refine ⟨hm.1, ?_⟩
    change (inner Real v ((c + s * t) • v + (A x : E3)) - c) / s ∈ Icc l u
    rw [hm.2, add_sub_cancel_left, mul_div_cancel_left₀ t hs]
    exact ht

end Poincare.Manifold.Schoenflies
