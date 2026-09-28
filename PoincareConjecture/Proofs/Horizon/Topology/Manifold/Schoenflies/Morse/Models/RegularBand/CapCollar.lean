import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.RegularBand.SpatialBoundaryAlignment
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.TwoCaps



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1


def boundedCylinderNorthernCap (v : E3) : Set E3 :=
  (fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
    {p : S2 | 0 ≤ inner Real v (p : E3)}


def boundedCylinderCapCollar (v : E3) (ε : Real) : Set E3 :=
  boundedCylinderNorthernCap v ∩
    {y | |‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ - 1| < ε}

theorem height_nonneg_of_mem_boundedCylinderNorthernCap {v y : E3}
    (hy : y ∈ boundedCylinderNorthernCap v) : 0 ≤ inner Real v y := by
  obtain ⟨p, hp, rfl⟩ := hy
  rw [inner_smul_right]
  exact mul_nonneg (boundedCylinderRadius_pos v p).le hp

private theorem mem_northernCap_of_height_norm_eq {v y z : E3}
    (hheight : inner Real v y = inner Real v z) (hnorm : ‖y‖ = ‖z‖)
    (hy : y ∈ boundedCylinderNorthernCap v) : z ∈ boundedCylinderNorthernCap v := by
  obtain ⟨p, hp, hpy⟩ := hy
  let r := boundedCylinderRadius v p
  have hr : 0 < r := boundedCylinderRadius_pos v p
  have hz : ‖z‖ = r := by
    rw [← hnorm, ← hpy, norm_smul]
    simp only [Real.norm_eq_abs, abs_of_pos (boundedCylinderRadius_pos v p),
      norm_eq_of_mem_sphere, mul_one]
    rfl
  let q : S2 := ⟨r⁻¹ • z, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr), hz, inv_mul_cancel₀ hr.ne']⟩
  have hqheight : inner Real v (q : E3) = inner Real v (p : E3) := by
    change inner Real v (r⁻¹ • z) = _
    rw [inner_smul_right, ← hheight, ← hpy, inner_smul_right]
    change r⁻¹ * (r * inner Real v (p : E3)) = _
    rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  have hqr : boundedCylinderRadius v q = r :=
    boundedCylinderRadius_eq_of_sq_height_eq v (by rw [hqheight])
  refine ⟨q, ?_, ?_⟩
  · change 0 ≤ inner Real v (q : E3)
    rw [hqheight]
    exact hp
  · change boundedCylinderRadius v q • (r⁻¹ • z) = z
    rw [hqr, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]



theorem boundedCylinderNorthernCap_mem_iff_of_height_projection_norm
    {v : E3} (hv : ‖v‖ = 1) {y z : E3}
    (hheight : inner Real v y = inner Real v z)
    (hprojection : ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ =
      ‖(Hemisphere.Plane v).orthogonalProjectionOnto z‖) :
    y ∈ boundedCylinderNorthernCap v ↔ z ∈ boundedCylinderNorthernCap v := by
  have hvv : inner Real v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
  have hnorm (x : E3) : ‖(Hemisphere.Plane v).orthogonalProjectionOnto x‖ ^ 2 =
      ‖x‖ ^ 2 - inner Real v x ^ 2 := by
    change ‖((Hemisphere.Plane v).orthogonalProjectionOnto x : E3)‖ ^ 2 = _
    rw [Submodule.coe_orthogonalProjectionOnto_apply, Submodule.starProjection_orthogonal_val,
      Submodule.starProjection_unit_singleton Real hv, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
      hvv, real_inner_comm x v, real_inner_self_eq_norm_sq]
    ring
  have hyz : ‖y‖ = ‖z‖ := by
    have hy := hnorm y
    have hz := hnorm z
    rw [hprojection, hheight] at hy
    nlinarith [norm_nonneg y, norm_nonneg z]
  exact ⟨mem_northernCap_of_height_norm_eq hheight hyz,
    mem_northernCap_of_height_norm_eq hheight.symm hyz.symm⟩

private theorem exists_radial_plane_coordinates
    {v : E3} (J : Hemisphere.Plane v ≃ₗᵢ[Real] E2)
    (x : Hemisphere.Plane v) (hx : 0 < ‖x‖) :
    ∃ p : S1, x = ‖x‖ • J.symm p := by
  let p : S1 := ⟨‖x‖⁻¹ • J x, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hx), J.norm_map, inv_mul_cancel₀ hx.ne']⟩
  refine ⟨p, ?_⟩
  apply J.injective
  rw [map_smul, J.apply_symm_apply]
  change J x = ‖x‖ • (‖x‖⁻¹ • J x)
  rw [smul_smul, mul_inv_cancel₀ hx.ne', one_smul]

private theorem height_radial_coordinates
    {v : E3} (hv : ‖v‖ = 1) (J : Hemisphere.Plane v ≃ₗᵢ[Real] E2)
    (t ρ : Real) (p : S1) :
    inner Real v (t • v + (ρ • J.symm p : Hemisphere.Plane v)) = t ∧
      ‖(Hemisphere.Plane v).orthogonalProjectionOnto
        (t • v + (ρ • J.symm p : Hemisphere.Plane v))‖ = |ρ| := by
  have hz := (heightCoordinates hv).symm_apply_apply (t, ρ • J.symm p)
  have hheight := congrArg Prod.fst hz
  have hproject := congrArg Prod.snd hz
  change (Hemisphere.Plane v).orthogonalProjectionOnto
    (t • v + (ρ • J.symm p : Hemisphere.Plane v)) = ρ • J.symm p at hproject
  refine ⟨hheight, ?_⟩
  rw [hproject]
  simp [norm_smul, Real.norm_eq_abs]

private theorem image_capCollar_of_radial_alignment
    {v : E3} (hv : ‖v‖ = 1) (J : Hemisphere.Plane v ≃ₗᵢ[Real] E2)
    (q : Diffeomorph (𝓡 1) (𝓡 1) S1 S1 ∞)
    (A B : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    {b c s ε : Real} (hbc : b ≤ c) (hs : 0 < s) (hε1 : ε < 1)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hD : ∀ (t : Real) (p : S1) (ρ : Real), b ≤ t → |ρ - 1| < ε →
      D (t • v + (B (ρ • J.symm (q p)) : E3)) = t • v + (A (ρ • J.symm p) : E3)) :
    D '' (liftPlaneDiffeomorph hv c s hs.ne' B '' boundedCylinderCapCollar v ε) =
      liftPlaneDiffeomorph hv c s hs.ne' A '' boundedCylinderCapCollar v ε := by
  have hcoords (y : E3) (hy : y ∈ boundedCylinderCapCollar v ε) :
      ∃ ρ : Real, ∃ p : S1, 0 < ρ ∧ |ρ - 1| < ε ∧
        (Hemisphere.Plane v).orthogonalProjectionOnto y = ρ • J.symm p := by
    have hr : 0 < ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ := by
      have := (abs_lt.mp (hy.2.trans hε1)).1
      linarith
    obtain ⟨p, hp⟩ := exists_radial_plane_coordinates J _ hr
    exact ⟨_, p, hr, hy.2, hp⟩
  have hrotate (y : E3) (hy : y ∈ boundedCylinderCapCollar v ε)
      (ρ : Real) (hρ : 0 < ρ)
      (hnorm : ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ = ρ) (p : S1) :
      inner Real v y • v + (ρ • J.symm p : Hemisphere.Plane v) ∈
        boundedCylinderCapCollar v ε := by
    have hz := height_radial_coordinates hv J (inner Real v y) ρ p
    have heq : ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ =
        ‖(Hemisphere.Plane v).orthogonalProjectionOnto
          (inner Real v y • v + (ρ • J.symm p : Hemisphere.Plane v))‖ := by
      rw [hnorm, hz.2, abs_of_pos hρ]
    exact ⟨(boundedCylinderNorthernCap_mem_iff_of_height_projection_norm hv hz.1.symm heq).mp
      hy.1, by
        change |‖(Hemisphere.Plane v).orthogonalProjectionOnto
          (inner Real v y • v + (ρ • J.symm p : Hemisphere.Plane v))‖ - 1| < ε
        rw [← heq]
        exact hy.2⟩
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨ρ, p, hρ, hρε, hproject⟩ := hcoords y hy
    have hnorm : ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ = ρ := by
      rw [hproject]
      simp [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    let z := inner Real v y • v + (ρ • J.symm (q.symm p) : Hemisphere.Plane v)
    have hz := height_radial_coordinates hv J (inner Real v y) ρ (q.symm p)
    refine ⟨z, hrotate y hy ρ hρ hnorm (q.symm p), ?_⟩
    rw [liftPlaneDiffeomorph_apply, liftPlaneDiffeomorph_apply, hproject]
    change (c + s * inner Real v z) • v +
      (A ((Hemisphere.Plane v).orthogonalProjectionOnto z) : E3) = _
    rw [hz.1]
    have hzproj : (Hemisphere.Plane v).orthogonalProjectionOnto z =
        ρ • J.symm (q.symm p) := congrArg Prod.snd
      ((heightCoordinates hv).symm_apply_apply (inner Real v y, ρ • J.symm (q.symm p)))
    rw [hzproj]
    simpa only [q.apply_symm_apply] using
      (hD _ (q.symm p) ρ (hbc.trans (le_add_of_nonneg_right
      (mul_nonneg hs.le (height_nonneg_of_mem_boundedCylinderNorthernCap hy.1)))) hρε).symm
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨ρ, p, hρ, hρε, hproject⟩ := hcoords z hz
    have hnorm : ‖(Hemisphere.Plane v).orthogonalProjectionOnto z‖ = ρ := by
      rw [hproject]
      simp [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    let y := inner Real v z • v + (ρ • J.symm (q p) : Hemisphere.Plane v)
    have hy := height_radial_coordinates hv J (inner Real v z) ρ (q p)
    refine ⟨liftPlaneDiffeomorph hv c s hs.ne' B y,
      ⟨y, hrotate z hz ρ hρ hnorm (q p), rfl⟩, ?_⟩
    rw [liftPlaneDiffeomorph_apply, liftPlaneDiffeomorph_apply, hproject]
    change D ((c + s * inner Real v y) • v +
      (B ((Hemisphere.Plane v).orthogonalProjectionOnto y) : E3)) = _
    rw [hy.1]
    have hyproj : (Hemisphere.Plane v).orthogonalProjectionOnto y =
        ρ • J.symm (q p) := congrArg Prod.snd
      ((heightCoordinates hv).symm_apply_apply (inner Real v z, ρ • J.symm (q p)))
    rw [hyproj]
    exact hD _ p ρ (hbc.trans (le_add_of_nonneg_right
      (mul_nonneg hs.le (height_nonneg_of_mem_boundedCylinderNorthernCap hz.1)))) hρε




theorem exists_upper_cap_collar_alignment
    {v : E3} (hv : ‖v‖ = 1)
    (γ : S1 → Hemisphere.Plane v)
    (hγ : _root_.Manifold.IsSmoothEmbedding (𝓡 1) 𝓘(Real, Hemisphere.Plane v) ∞ γ)
    (A B : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (hA : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (hB : B '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    {a b c s : Real} (hab : a < b) (hbc : b ≤ c) (hs : 0 < s) :
    ∃ ε : Real, 0 < ε ∧ ε < 1 ∧
      ∃ D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ x, inner Real v (D x) = inner Real v x) ∧
        (∀ x, inner Real v x ≤ a → D x = x) ∧
        (∀ (t : Real) (p : S1), D (t • v + (γ p : E3)) = t • v + (γ p : E3)) ∧
        D '' (liftPlaneDiffeomorph hv c s hs.ne' B '' boundedCylinderCapCollar v ε) =
          liftPlaneDiffeomorph hv c s hs.ne' A '' boundedCylinderCapCollar v ε := by
  obtain ⟨J, q, _, ε, hε, hε1, _, _, D, hDheight, hDlower, _, hDcylinder, hDgerm⟩ :=
    exists_spatial_upper_boundary_alignment_of_fillings hv γ hγ A B hA hB hab
  exact ⟨ε, hε, hε1, D, hDheight, hDlower, hDcylinder,
    image_capCollar_of_radial_alignment hv J q A B hbc hs hε1 D hDgerm⟩

end Poincare.Manifold.Schoenflies
