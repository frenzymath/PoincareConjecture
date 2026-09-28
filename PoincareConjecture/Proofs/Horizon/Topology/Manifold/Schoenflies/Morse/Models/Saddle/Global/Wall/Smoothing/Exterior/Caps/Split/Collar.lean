import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Split.Body
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.CapGraph.Belt

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Split

open Poincare.Topology Poincare.Geometry.Euclidean

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem norm_projection_le_of_mem_capBody {v y : E3} (hv : ‖v‖ = 1)
    (hy : y ∈ capBody v) : ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ ≤ 1 := by
  obtain ⟨⟨p, t, ht, htr, rfl⟩, _⟩ := hy
  have hb := norm_boundedCylinder_projection_le v hv p
  rw [map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (boundedCylinderRadius_pos v p)] at hb
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  exact (mul_le_mul_of_nonneg_right htr (norm_nonneg _)).trans hb

private theorem exists_norm_smul_unit (y : E3) : ∃ p : S2, y = ‖y‖ • (p : E3) := by
  by_cases hy : y = 0
  · obtain ⟨p, hp⟩ := NormedSpace.sphere_nonempty (E := E3).mpr
      (show (0 : Real) ≤ 1 by norm_num)
    exact ⟨⟨p, hp⟩, by simp [hy]⟩
  · refine ⟨((homeomorphUnitSphereProd E3) ⟨y, hy⟩).1, ?_⟩
    rw [homeomorphUnitSphereProd_apply_fst_coe, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hy), one_smul]

theorem mem_capBody_iff_of_height_lt_one {v y : E3} (hv : ‖v‖ = 1)
    (hy : inner Real v y < 1) :
    y ∈ capBody v ↔
      0 ≤ inner Real v y ∧ ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ ≤ 1 := by
  constructor
  · intro hybody
    exact ⟨hybody.2, norm_projection_le_of_mem_capBody hv hybody⟩
  · rintro ⟨hy0, hynorm⟩
    obtain ⟨p, hp⟩ := exists_norm_smul_unit y
    refine ⟨⟨p, ‖y‖, norm_nonneg y, ?_, hp⟩, hy0⟩
    by_contra hle
    have hlt : boundedCylinderRadius v p < ‖y‖ := lt_of_not_ge hle
    have hyn : 0 < ‖y‖ := (boundedCylinderRadius_pos v p).trans hlt
    have hpheight : 0 ≤ inner Real v (p : E3) := by
      have hh : 0 ≤ ‖y‖ * inner Real v (p : E3) := by
        calc
          0 ≤ inner Real v y := hy0
          _ = ‖y‖ * inner Real v (p : E3) := by conv_lhs => rw [hp, inner_smul_right]
      nlinarith
    have hboundaryheight : inner Real v (boundedCylinderRadius v p • (p : E3)) < 1 := by
      calc
        _ = boundedCylinderRadius v p * inner Real v (p : E3) := inner_smul_right _ _ _
        _ ≤ ‖y‖ * inner Real v (p : E3) :=
          mul_le_mul_of_nonneg_right hlt.le hpheight
        _ = inner Real v y := by conv_rhs => rw [hp, inner_smul_right]
        _ < 1 := hy
    have hboundary : boundedCylinderRadius v p • (p : E3) ∈
        boundedCylinderNorthernCap v := ⟨p, hpheight, rfl⟩
    have hb := ((mem_boundedCylinderNorthernCap_iff_of_height_lt_one hv
      hboundaryheight).mp hboundary).2
    rw [map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos (boundedCylinderRadius_pos v p)] at hb
    have hpy : ‖y‖ * ‖(Hemisphere.Plane v).orthogonalProjectionOnto (p : E3)‖ ≤ 1 := by
      calc
        _ = ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ := by
          conv_rhs => rw [hp, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hyn]
        _ ≤ 1 := hynorm
    have hpn : 0 < ‖(Hemisphere.Plane v).orthogonalProjectionOnto (p : E3)‖ := by
      nlinarith [norm_nonneg ((Hemisphere.Plane v).orthogonalProjectionOnto (p : E3))]
    nlinarith [mul_pos (sub_pos.mpr hlt) hpn]

theorem capBody_slice_eq_disk {v : E3} (hv : ‖v‖ = 1)
    {t : Real} (ht : t ∈ Ico (0 : Real) 1) :
    capBody v ∩ {y | inner Real v y = t} =
      (fun x : Hemisphere.Plane v => t • v + (x : E3)) ''
        closedBall (0 : Hemisphere.Plane v) 1 := by
  ext y
  constructor
  · rintro ⟨hy, hh⟩
    refine ⟨(Hemisphere.Plane v).orthogonalProjectionOnto y,
      mem_closedBall_zero_iff.mpr (norm_projection_le_of_mem_capBody hv hy), ?_⟩
    have he := (heightCoordinates hv).apply_symm_apply y
    change inner Real v y • v + ((Hemisphere.Plane v).orthogonalProjectionOnto y : E3) = y at he
    rwa [hh] at he
  · rintro ⟨x, hx, rfl⟩
    have hh : inner Real v (t • v + (x : E3)) = t := inner_heightCoordinates hv (t, x)
    have hp : (Hemisphere.Plane v).orthogonalProjectionOnto (t • v + (x : E3)) = x :=
      congrArg Prod.snd ((heightCoordinates hv).symm_apply_apply (t, x))
    refine ⟨(mem_capBody_iff_of_height_lt_one hv (by rw [hh]; exact ht.2)).mpr ?_, hh⟩
    exact ⟨by rw [hh]; exact ht.1, by rw [hp]; exact mem_closedBall_zero_iff.mp hx⟩

theorem capSide_slice_eq_halfDisk {v w : E3} (hv : ‖v‖ = 1)
    (hw : inner Real w v = 0) {t : Real} (ht : t ∈ Ico (0 : Real) 1) :
    capSide v w ∩ {y | inner Real v y = t} =
      (fun x : Hemisphere.Plane v => t • v + (x : E3)) ''
        (closedBall (0 : Hemisphere.Plane v) 1 ∩ {x | inner Real w (x : E3) ≤ 0}) := by
  have hh (x : Hemisphere.Plane v) :
      inner Real w (t • v + (x : E3)) = inner Real w (x : E3) := by
    simp only [inner_add_right, inner_smul_right, hw, mul_zero, zero_add]
  ext y
  constructor
  · rintro ⟨⟨hy, hwy⟩, hty⟩
    obtain ⟨x, hx, rfl⟩ := (Set.ext_iff.mp (capBody_slice_eq_disk hv ht) y).mp ⟨hy, hty⟩
    exact ⟨x, ⟨hx, by simpa only [mem_ofPred_eq, hh] using hwy⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hwx⟩, rfl⟩
    obtain ⟨hy, hty⟩ := (Set.ext_iff.mp (capBody_slice_eq_disk hv ht)
      (t • v + (x : E3))).mpr ⟨x, hx, rfl⟩
    exact ⟨⟨hy, by simpa only [mem_ofPred_eq, hh] using hwx⟩, hty⟩

theorem wallSection_slice_eq_diameter {v w : E3} (hv : ‖v‖ = 1)
    (hw : inner Real w v = 0) {t : Real} (ht : t ∈ Ico (0 : Real) 1) :
    wallSection v w ∩ {y | inner Real v y = t} =
      (fun x : Hemisphere.Plane v => t • v + (x : E3)) ''
        (closedBall (0 : Hemisphere.Plane v) 1 ∩ {x | inner Real w (x : E3) = 0}) := by
  have hh (x : Hemisphere.Plane v) :
      inner Real w (t • v + (x : E3)) = inner Real w (x : E3) := by
    simp only [inner_add_right, inner_smul_right, hw, mul_zero, zero_add]
  ext y
  constructor
  · rintro ⟨⟨hy, hwy⟩, hty⟩
    obtain ⟨x, hx, rfl⟩ := (Set.ext_iff.mp (capBody_slice_eq_disk hv ht) y).mp ⟨hy, hty⟩
    exact ⟨x, ⟨hx, by simpa only [mem_ofPred_eq, hh] using hwy⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hwx⟩, rfl⟩
    obtain ⟨hy, hty⟩ := (Set.ext_iff.mp (capBody_slice_eq_disk hv ht)
      (t • v + (x : E3))).mpr ⟨x, hx, rfl⟩
    exact ⟨⟨hy, by simpa only [mem_ofPred_eq, hh] using hwx⟩, hty⟩

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Split
