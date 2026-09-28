import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapCollar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.RadialBody








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Split

open Poincare.Topology

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1


def capBody (v : E3) : Set E3 :=
  radialClosedBody (boundedCylinderRadius v) ∩ {y | 0 ≤ inner Real v y}


def baseDisk (v : E3) : Set E3 :=
  closedBall (0 : E3) 1 ∩ {y | inner Real v y = 0}


def capSide (v w : E3) : Set E3 := capBody v ∩ {y | inner Real w y ≤ 0}


def wallSection (v w : E3) : Set E3 := capBody v ∩ {y | inner Real w y = 0}


def radialCoordinates (v : E3) : E3 ≃ₜ E3 :=
  radialHomeomorph (boundedCylinderRadius v)
    (contMDiff_boundedCylinderRadius v).continuous (boundedCylinderRadius_pos v)

theorem radialCoordinates_positive_factor (v x : E3) :
    ∃ k : Real, 0 < k ∧ radialCoordinates v x = k • x := by
  by_cases hx : x = 0
  · subst x
    exact ⟨1, zero_lt_one, by simp [radialCoordinates, radialHomeomorph]⟩
  · exact ⟨_, boundedCylinderRadius_pos v _, by
      change radialMap (boundedCylinderRadius v) x = _
      rw [radialMap, dif_neg hx]⟩

theorem inner_radialCoordinates_nonneg_iff (v w x : E3) :
    0 ≤ inner Real w (radialCoordinates v x) ↔ 0 ≤ inner Real w x := by
  obtain ⟨k, hk, he⟩ := radialCoordinates_positive_factor v x
  rw [he, inner_smul_right, mul_nonneg_iff_of_pos_left hk]

theorem inner_radialCoordinates_nonpos_iff (v w x : E3) :
    inner Real w (radialCoordinates v x) ≤ 0 ↔ inner Real w x ≤ 0 := by
  obtain ⟨k, hk, he⟩ := radialCoordinates_positive_factor v x
  rw [he, inner_smul_right]
  constructor <;> intro h <;> nlinarith

theorem inner_radialCoordinates_zero_iff (v w x : E3) :
    inner Real w (radialCoordinates v x) = 0 ↔ inner Real w x = 0 := by
  obtain ⟨k, hk, he⟩ := radialCoordinates_positive_factor v x
  rw [he, inner_smul_right, mul_eq_zero]
  simp [hk.ne']

theorem radialCoordinates_image_upperHalfBall (v : E3) :
    radialCoordinates v ''
      (closedBall (0 : E3) 1 ∩ {y | 0 ≤ inner Real v y}) = capBody v := by
  have hbody := radialHomeomorph_image_closedBall (boundedCylinderRadius v)
    (contMDiff_boundedCylinderRadius v).continuous (boundedCylinderRadius_pos v)
  change radialCoordinates v '' closedBall (0 : E3) 1 = _ at hbody
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hh⟩, rfl⟩
    exact ⟨hbody ▸ mem_image_of_mem _ hx,
      (inner_radialCoordinates_nonneg_iff v v x).2 hh⟩
  · rintro ⟨hy, hh⟩
    obtain ⟨x, hx, rfl⟩ := hbody.symm ▸ hy
    exact ⟨x, ⟨hx, (inner_radialCoordinates_nonneg_iff v v x).1 hh⟩, rfl⟩

theorem radialCoordinates_image_upperHemisphere (v : E3) :
    radialCoordinates v ''
      (sphere (0 : E3) 1 ∩ {y | 0 ≤ inner Real v y}) =
        boundedCylinderNorthernCap v := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hh⟩, rfl⟩
    exact ⟨⟨x, hx⟩, hh, (radialMap_sphere _ ⟨x, hx⟩).symm⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, ⟨p.property, hp⟩, radialMap_sphere _ p⟩

theorem radialCoordinates_eq_self_of_height_zero (v : E3) {x : E3}
    (hx : inner Real v x = 0) : radialCoordinates v x = x := by
  by_cases hx0 : x = 0
  · subst x
    exact radialMap_zero _
  let p := ((homeomorphUnitSphereProd E3) ⟨x, hx0⟩).1
  have hp : inner Real v (p : E3) = 0 := by
    change inner Real v ((homeomorphUnitSphereProd E3) ⟨x, hx0⟩).1 = 0
    rw [homeomorphUnitSphereProd_apply_fst_coe]
    rw [inner_smul_right, hx, mul_zero]
  have hr : boundedCylinderRadius v p = 1 := by
    rw [boundedCylinderRadius_of_abs_height_le v p (by rw [hp]; norm_num), hp]
    norm_num
  change radialMap (boundedCylinderRadius v) x = x
  rw [radialMap, dif_neg hx0]
  change boundedCylinderRadius v p • x = x
  rw [hr, one_smul]

theorem radialCoordinates_image_baseDisk (v : E3) :
    radialCoordinates v '' baseDisk v = baseDisk v := by
  rw [image_congr (fun _ hx => radialCoordinates_eq_self_of_height_zero v hx.2), image_id']

theorem capBody_inter_base (v : E3) :
    capBody v ∩ {y | inner Real v y = 0} = baseDisk v := by
  rw [← radialCoordinates_image_upperHalfBall]
  ext y
  constructor
  · rintro ⟨⟨x, ⟨hx, _⟩, rfl⟩, hh⟩
    have hx0 := (inner_radialCoordinates_zero_iff v v x).1 hh
    rw [radialCoordinates_eq_self_of_height_zero v hx0]
    exact ⟨hx, hx0⟩
  · rintro ⟨hy, hh⟩
    exact ⟨⟨y, ⟨hy, hh.ge⟩, radialCoordinates_eq_self_of_height_zero v hh⟩, hh⟩

theorem isCompact_capBody (v : E3) : IsCompact (capBody v) := by
  rw [← radialCoordinates_image_upperHalfBall]
  exact ((isCompact_closedBall (0 : E3) 1).inter_right
    (isClosed_le continuous_const (innerSL Real v).continuous)).image
      (radialCoordinates v).continuous

theorem capSide_union (v w : E3) : capSide v w ∪ capSide v (-w) = capBody v := by
  ext y
  simp only [capSide, mem_union, mem_inter_iff, mem_setOf_eq, inner_neg_left]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro hy
    rcases le_total (inner Real w y) 0 with hw | hw
    · exact Or.inl ⟨hy, hw⟩
    · exact Or.inr ⟨hy, by linarith⟩

theorem capSide_inter (v w : E3) :
    capSide v w ∩ capSide v (-w) = wallSection v w := by
  ext y
  simp only [capSide, wallSection, mem_inter_iff, mem_setOf_eq, inner_neg_left]
  constructor
  · rintro ⟨⟨hy, hleft⟩, _, hright⟩
    exact ⟨hy, by linarith⟩
  · rintro ⟨hy, hw⟩
    exact ⟨⟨hy, hw.le⟩, hy, by rw [hw]; norm_num⟩



theorem wallSection_eq_radial_halfDisk (v w : E3) :
    wallSection v w =
      (fun x : Hemisphere.Plane w => radialCoordinates v (x : E3)) ''
        (closedBall (0 : Hemisphere.Plane w) 1 ∩
          {x | 0 ≤ inner Real v (x : E3)}) := by
  rw [wallSection, ← radialCoordinates_image_upperHalfBall]
  ext y
  constructor
  · rintro ⟨⟨x, ⟨hx, hv⟩, rfl⟩, hw⟩
    have hxw : x ∈ Hemisphere.Plane w :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        ((inner_radialCoordinates_zero_iff v w x).1 hw)
    exact ⟨⟨x, hxw⟩, ⟨by simpa using hx, hv⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hv⟩, rfl⟩
    exact ⟨⟨x, ⟨by simpa using hx, hv⟩, rfl⟩,
      (inner_radialCoordinates_zero_iff v w x).2
        (Submodule.mem_orthogonal_singleton_iff_inner_right.mp x.property)⟩

theorem continuous_wallSection_param (v w : E3) :
    Continuous (fun x : Hemisphere.Plane w => radialCoordinates v (x : E3)) :=
  (radialCoordinates v).continuous.comp continuous_subtype_val

theorem injective_wallSection_param (v w : E3) :
    Injective (fun x : Hemisphere.Plane w => radialCoordinates v (x : E3)) :=
  (radialCoordinates v).injective.comp Subtype.val_injective

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Split
