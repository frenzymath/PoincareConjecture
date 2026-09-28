import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.ProfileGeometry
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Extremum.BandStraightening



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1



theorem image_minimum_profile_disk {v : E3} (c r : Real)
    (J : E2 ≃ₗᵢ[Real] Hemisphere.Plane v) (f : S2 → E3)
    (e : OpenPartialHomeomorph E2 S2) (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hprofile : ∀ x ∈ closedBall (0 : E2) (7 * r / 8),
      D (f (e x)) =
        ((Real.sqrt (minimumCapDenominator (‖x‖ ^ 2 / r ^ 2)))⁻¹ • J x : Hemisphere.Plane v) +
          (c + ‖x‖ ^ 2) • v) :
    D '' (f '' (e '' closedBall (0 : E2) (7 * r / 8))) = quadraticMinimumCap v c r := by
  have hball : J '' closedBall (0 : E2) (7 * r / 8) =
      closedBall (0 : Hemisphere.Plane v) (7 * r / 8) := by
    rw [J.image_closedBall, map_zero]
  unfold quadraticMinimumCap
  rw [← hball, image_image, image_image, image_image]
  apply image_congr
  intro x hx
  simpa only [quadraticMinimumCapPoint, J.norm_map] using hprofile x hx

theorem quadraticMinimumCap_height_le {v : E3} (hv : ‖v‖ = 1)
    (c : Real) {r : Real} (hr : 0 < r) {y : E3} (hy : y ∈ quadraticMinimumCap v c r) :
    inner Real v y ≤ c + (7 * r / 8) ^ 2 := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [inner_quadraticMinimumCapPoint hv]
  have hn : ‖x‖ ≤ 7 * r / 8 := mem_closedBall_zero_iff.mp hx
  nlinarith [norm_nonneg x]



theorem closed_disk_top_level_eq_boundary (d : E2 → S2) (h : S2 → Real) (b : Real)
    (hboundary : ∀ x ∈ sphere (0 : E2) 1, h (d x) = b)
    (hinterior : ∀ p ∈ d '' ball (0 : E2) 1, h p < b) :
    (d '' closedBall (0 : E2) 1) ∩ h ⁻¹' {b} = d '' sphere (0 : E2) 1 := by
  ext p
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hh⟩
    have hn := mem_closedBall_zero_iff.mp hx
    have heq : ‖x‖ = 1 := by
      by_contra he
      have hxball : x ∈ ball (0 : E2) 1 := mem_ball_zero_iff.mpr (lt_of_le_of_ne hn he)
      have hlt := hinterior (d x) ⟨x, hxball, rfl⟩
      exact (ne_of_lt hlt) hh
    exact ⟨x, mem_sphere_zero_iff_norm.mpr heq, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, sphere_subset_closedBall hx, rfl⟩, hboundary x hx⟩



theorem image_minimum_disk_top_boundary {v : E3} (hv : ‖v‖ = 1)
    {c r b : Real} (hr : 0 < r) (hab : c + (7 * r / 8) ^ 2 < b)
    (f : S2 → E3) (K C : Set S2)
    (hC : K ∩ (fun p => inner Real v (f p)) ⁻¹' {b} = C)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ y, inner Real v (D y) = inner Real v y)
    (himage : D '' (f '' K) = quadraticMinimumCap v c r ∪
      (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
        (Icc (c + (7 * r / 8) ^ 2) b ×ˢ sphere (0 : Hemisphere.Plane v) r)) :
    D '' (f '' C) = (fun q : Hemisphere.Plane v => b • v + (q : E3)) ''
      sphere (0 : Hemisphere.Plane v) r := by
  have hh (t : Real) (q : Hemisphere.Plane v) : inner Real v (t • v + (q : E3)) = t :=
    congrArg Prod.fst ((Poincare.Geometry.Euclidean.heightCoordinates hv).symm_apply_apply (t, q))
  apply Subset.antisymm
  · rintro y ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    rw [← hC] at hp
    have hmem : D (f p) ∈ quadraticMinimumCap v c r ∪
        (fun z : Real × Hemisphere.Plane v => z.1 • v + (z.2 : E3)) ''
          (Icc (c + (7 * r / 8) ^ 2) b ×ˢ sphere (0 : Hemisphere.Plane v) r) := by
      rw [← himage]
      exact ⟨f p, ⟨p, hp.1, rfl⟩, rfl⟩
    have hbheight : inner Real v (D (f p)) = b := (hDheight _).trans hp.2
    rcases hmem with hcap | ⟨⟨t, q⟩, ⟨ht, hq⟩, he⟩
    · have hbnd := quadraticMinimumCap_height_le hv c hr hcap
      rw [hbheight] at hbnd
      exact (not_le_of_gt hab hbnd).elim
    · have ht' : t = b := by rw [← he, hh] at hbheight; exact hbheight
      exact ⟨q, hq, by simpa only [ht'] using he⟩
  · rintro y ⟨q, hq, rfl⟩
    have hmem : b • v + (q : E3) ∈ D '' (f '' K) := by
      rw [himage]
      exact Or.inr ⟨(b, q), ⟨⟨hab.le, le_rfl⟩, hq⟩, rfl⟩
    obtain ⟨_, ⟨p, hp, rfl⟩, he⟩ := hmem
    refine ⟨f p, ⟨p, ?_, rfl⟩, he⟩
    rw [← hC]
    refine ⟨hp, ?_⟩
    change inner Real v (f p) = b
    rw [← hDheight, he, hh]

end Poincare.Manifold.Schoenflies
