import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Assembly.Replacement.Model.CapGeometry



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Reverse

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1

open Poincare.Geometry.Euclidean

theorem mem_extended_cap_of_clock_interval
    {v : E3} (b s : Real) (γ : S1 → Hemisphere.Plane v) (g : E2 → E3)
    {η r : Real} (hr : 1 < r) (hrη : r - 1 < η)
    (hcollar : ∀ q : S1, ∀ ρ : Real, |ρ - 1| < η →
      g (ρ • (q : E2)) = (b + s * capCollarClock ρ) • v + (γ q : E3))
    (q : S1) {t : Real} (ht : t ∈ Icc (capCollarClock r) 0) :
    (b + s * t) • v + (γ q : E3) ∈ g '' closedBall (0 : E2) r := by
  obtain ⟨ρ, hρ, he⟩ := exists_capCollarClock_preimage hr.le ht
  refine ⟨ρ • (q : E2), ?_, ?_⟩
  · rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by linarith [hρ.1] : 0 < ρ), norm_eq_of_mem_sphere, mul_one]
    exact hρ.2
  · rw [hcollar q ρ (by rw [abs_of_nonneg (by linarith [hρ.1])]; linarith [hρ.2]), he]

theorem extended_cap_subset_opposite_union_core
    {v : E3} (hv : ‖v‖ = 1) (b s d : Real) (hs : s ≠ 0) (hd : d ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (γ : S1 → Hemisphere.Plane v)
    (hboundary : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (g : E2 → E3) {η r : Real} (hr : 1 < r) (hrη : r - 1 < η)
    (hdscale : d = s * capCollarClock r)
    (hcollar : ∀ q : S1, ∀ ρ : Real, |ρ - 1| < η →
      g (ρ • (q : E2)) = (b + s * capCollarClock ρ) • v + (γ q : E3)) :
    g '' closedBall (0 : E2) r ⊆
      (liftPlaneDiffeomorph hv b d hd A '' boundedCylinderNorthernCap v) ∪
        (g '' closedBall (0 : E2) 1) := by
  rintro _ ⟨x, hx, rfl⟩
  by_cases hx1 : ‖x‖ ≤ 1
  · exact Or.inr (mem_image_of_mem g (mem_closedBall_zero_iff.mpr hx1))
  have hxpos : 0 < ‖x‖ := by linarith
  let q : S1 := ⟨‖x‖⁻¹ • x, by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hxpos), inv_mul_cancel₀ hxpos.ne']⟩
  have hxq : ‖x‖ • (q : E2) = x := by
    change ‖x‖ • (‖x‖⁻¹ • x) = x
    rw [smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul]
  have hxr : ‖x‖ ∈ Icc 1 r := ⟨le_of_not_ge hx1, mem_closedBall_zero_iff.mp hx⟩
  obtain ⟨z, hz, hzq⟩ := hboundary.symm ▸ mem_range_self q
  have hclock := capCollarClock_neg_of_one_lt hr
  have hlow := capCollarClock_antitone hxpos hxr.2
  have hhigh : capCollarClock ‖x‖ ≤ 0 := by
    simpa using capCollarClock_antitone (by norm_num : (0 : Real) < 1) hxr.1
  apply Or.inl
  rw [← hxq, hcollar q ‖x‖ (by
    rw [abs_of_nonneg (by linarith [hxr.1])]
    linarith [hxr.2]), ← hzq]
  have hcoord : (b + s * capCollarClock ‖x‖) • v + (A z : E3) =
      capCoordinates hv A (z, b + s * capCollarClock ‖x‖) :=
    (capCoordinates_apply hv A (z, b + s * capCollarClock ‖x‖)).symm
  rw [hcoord, transported_cap_boundary_fiber_iff hv b d hd A z
    (mem_sphere_zero_iff_norm.mp hz)]
  have hquot : (b + s * capCollarClock ‖x‖ - b) / d =
      capCollarClock ‖x‖ / capCollarClock r := by
    rw [hdscale]
    field_simp
    ring
  rw [hquot]
  exact ⟨div_nonneg_of_nonpos hhigh hclock.le,
    (div_le_iff_of_neg hclock).mpr (by simpa using hlow)⟩

theorem opposite_cap_circle_point_mem_extended
    {v : E3} (hv : ‖v‖ = 1) (b s d : Real) (hs : s ≠ 0) (hd : d ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (γ : S1 → Hemisphere.Plane v)
    (hboundary : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (g : E2 → E3) {η r : Real} (hr : 1 < r) (hrη : r - 1 < η)
    (hdscale : d = s * capCollarClock r)
    (hcollar : ∀ q : S1, ∀ ρ : Real, |ρ - 1| < η →
      g (ρ • (q : E2)) = (b + s * capCollarClock ρ) • v + (γ q : E3))
    {y : E3} (hy : y ∈ liftPlaneDiffeomorph hv b d hd A '' boundedCylinderNorthernCap v)
    (hyproj : (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' sphere 0 1) :
    y ∈ g '' closedBall (0 : E2) r := by
  obtain ⟨z, hz, hzy⟩ := hyproj
  have hcoord : capCoordinates hv A (z, inner Real v y) = y := by
    rw [capCoordinates_apply, hzy]
    exact (heightCoordinates hv).apply_symm_apply y
  have hnorm : (inner Real v y - b) / d ∈ Icc (0 : Real) 1 := by
    rw [← hcoord] at hy
    exact (transported_cap_boundary_fiber_iff hv b d hd A z
      (mem_sphere_zero_iff_norm.mp hz) _).mp hy
  let t := (inner Real v y - b) / s
  have hquot : (inner Real v y - b) / d = t / capCollarClock r := by
    dsimp [t]
    rw [hdscale]
    field_simp
  rw [hquot] at hnorm
  have hclock := capCollarClock_neg_of_one_lt hr
  have ht : t ∈ Icc (capCollarClock r) 0 :=
    ⟨by simpa using (div_le_iff_of_neg hclock).mp hnorm.2,
      by simpa using (le_div_iff_of_neg hclock).mp hnorm.1⟩
  obtain ⟨q, hq⟩ := hboundary ▸ mem_image_of_mem A hz
  have hmem := mem_extended_cap_of_clock_interval b s γ g hr hrη hcollar q ht
  have htval : b + s * t = inner Real v y := by dsimp [t]; field_simp; ring
  rw [htval, hq] at hmem
  rwa [← capCoordinates_apply hv A (z, inner Real v y), hcoord] at hmem

end Poincare.Manifold.Schoenflies.Reverse
