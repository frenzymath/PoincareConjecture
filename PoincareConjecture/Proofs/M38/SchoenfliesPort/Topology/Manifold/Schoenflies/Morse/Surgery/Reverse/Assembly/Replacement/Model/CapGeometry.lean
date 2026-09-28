import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Contact.FlatCaps
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Models.CapTruncation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CappedCylinder







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.Reverse
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Reverse

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

open Poincare.Geometry.Euclidean

theorem capCollarClock_neg_of_one_lt {r : Real} (hr : 1 < r) : capCollarClock r < 0 := by
  apply div_neg_of_neg_of_pos
  · nlinarith
  · linarith

theorem transported_cap_bounds
    {v : E3} (hv : ‖v‖ = 1) (b s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    {y : E3} (hy : y ∈ liftPlaneDiffeomorph hv b s hs A '' boundedCylinderNorthernCap v) :
    0 ≤ (inner Real v y - b) / s ∧
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' closedBall 0 1 ∧
      |inner Real v y - b| ≤ 2 * |s| := by
  obtain ⟨z, ⟨p, hp, rfl⟩, rfl⟩ := hy
  rw [inner_liftPlaneDiffeomorph, projection_liftPlaneDiffeomorph,
    add_sub_cancel_left, mul_div_cancel_left₀ _ hs]
  refine ⟨?_, mem_image_of_mem A (mem_closedBall_zero_iff.mpr
    (norm_boundedCylinder_projection_le v hv p)), ?_⟩
  · rw [inner_smul_right]
    exact mul_nonneg (boundedCylinderRadius_pos v p).le hp
  · rw [abs_mul]
    nlinarith [abs_boundedCylinder_height_le v hv p, abs_nonneg s]

theorem transported_cap_boundary_fiber_iff
    {v : E3} (hv : ‖v‖ = 1) (b s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (q : Hemisphere.Plane v) (hq : ‖q‖ = 1) (t : Real) :
    capCoordinates hv A (q, t) ∈
        liftPlaneDiffeomorph hv b s hs A '' boundedCylinderNorthernCap v ↔
      (t - b) / s ∈ Icc (0 : Real) 1 := by
  let x : E3 := ((t - b) / s) • v + (q : E3)
  have hproj : (Hemisphere.Plane v).orthogonalProjectionOnto x = q := by simp [x]
  have hheight : inner Real v x = (t - b) / s := by
    simp [x, inner_add_right, inner_smul_right, hv,
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp q.property]
  have hmap : liftPlaneDiffeomorph hv b s hs A x = capCoordinates hv A (q, t) := by
    rw [liftPlaneDiffeomorph_apply, hheight, hproj, capCoordinates_apply]
    congr 2
    field_simp
    ring
  have hmem : liftPlaneDiffeomorph hv b s hs A x ∈
      liftPlaneDiffeomorph hv b s hs A '' boundedCylinderNorthernCap v ↔
        x ∈ boundedCylinderNorthernCap v := by
    constructor
    · rintro ⟨z, hz, he⟩
      exact (liftPlaneDiffeomorph hv b s hs A).injective he ▸ hz
    · exact mem_image_of_mem _
  rw [← hmap, hmem, mem_boundedCylinderNorthernCap_iff_boundary_height hv
    (by rw [hproj, hq]), hheight]

theorem transported_cap_zero_projection
    {v : E3} (hv : ‖v‖ = 1) (b s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    {y : E3} (hy : y ∈ liftPlaneDiffeomorph hv b s hs A '' boundedCylinderNorthernCap v)
    (hzero : inner Real v y = b) :
    (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' sphere 0 1 := by
  obtain ⟨z, ⟨p, hp, rfl⟩, rfl⟩ := hy
  rw [inner_liftPlaneDiffeomorph] at hzero
  have ht : inner Real v (boundedCylinderRadius v p • (p : E3)) = 0 := by
    have hm : s * inner Real v (boundedCylinderRadius v p • (p : E3)) = 0 := by linarith
    exact (mul_eq_zero.mp hm).resolve_left hs
  rw [projection_liftPlaneDiffeomorph]
  exact mem_image_of_mem A (mem_sphere_zero_iff_norm.mpr
    (norm_boundedCylinder_projection_eq_one_of_height_belt v hv p (by rw [ht]; norm_num)))



theorem exists_ambient_two_caps_of_opposite_scales
    {v : E3} (hv : ‖v‖ = 1) (b s d : Real) (hs : s ≠ 0) (hd : d ≠ 0)
    (hopposite : s * d < 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      F '' sphere (0 : E3) 1 =
        (liftPlaneDiffeomorph hv b d hd A '' boundedCylinderNorthernCap v) ∪
        (liftPlaneDiffeomorph hv b s hs A '' boundedCylinderNorthernCap v) := by
  let Z : Set E3 := (fun z : Real × Hemisphere.Plane v => z.1 • v + (A z.2 : E3)) ''
    (Icc b b ×ˢ sphere (0 : Hemisphere.Plane v) 1)
  have hZ (k : Real) (hk : k ≠ 0) :
      Z ⊆ liftPlaneDiffeomorph hv b k hk A '' boundedCylinderNorthernCap v := by
    rintro _ ⟨⟨t, q⟩, ⟨ht, hq⟩, rfl⟩
    have htb : t = b := le_antisymm ht.2 ht.1
    subst t
    simpa only [capCoordinates_apply] using
      (transported_cap_boundary_fiber_iff hv b k hk A q
        (mem_sphere_zero_iff_norm.mp hq) b).mpr (by simp)
  rcases lt_or_gt_of_ne hs with hneg | hpos
  · have hdpos : 0 < d := by nlinarith
    obtain ⟨F, hF⟩ := exists_ambient_capped_cylinder_of_scales hv b b le_rfl
      (-s) d (neg_pos.mpr hneg) hdpos A
    refine ⟨F, ?_⟩
    change F '' sphere (0 : E3) 1 = _ at hF
    simp only [neg_neg] at hF
    change F '' sphere (0 : E3) 1 =
      ((liftPlaneDiffeomorph hv b s hs A '' boundedCylinderNorthernCap v) ∪ Z) ∪
        (liftPlaneDiffeomorph hv b d hd A '' boundedCylinderNorthernCap v) at hF
    rw [union_eq_left.mpr (hZ s hs), union_comm] at hF
    exact hF
  · have hdneg : d < 0 := by nlinarith
    obtain ⟨F, hF⟩ := exists_ambient_capped_cylinder_of_scales hv b b le_rfl
      (-d) s (neg_pos.mpr hdneg) hpos A
    refine ⟨F, ?_⟩
    simp only [neg_neg] at hF
    change F '' sphere (0 : E3) 1 =
      ((liftPlaneDiffeomorph hv b d hd A '' boundedCylinderNorthernCap v) ∪ Z) ∪
        (liftPlaneDiffeomorph hv b s hs A '' boundedCylinderNorthernCap v) at hF
    rw [union_eq_left.mpr (hZ d hd)] at hF
    exact hF

end Poincare.Manifold.Schoenflies.Reverse

end

end M38Schoenflies
