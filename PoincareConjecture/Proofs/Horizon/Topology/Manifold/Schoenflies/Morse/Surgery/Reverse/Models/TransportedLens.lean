import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Models.MarkedLens
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Models.CapTruncation



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Reverse

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : E3) 1

open Poincare.Geometry.Euclidean

theorem radialBody_markedLens_bounds (v : E3) (hv : ‖v‖ = 1)
    (edge width : Real) {y : E3}
    (hy : y ∈ Poincare.Topology.radialClosedBody (markedLensRadius v edge width)) :
    ‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ ≤ 1 ∧
      |inner Real v y| ≤ 2 := by
  obtain ⟨p, t, ht, htr, rfl⟩ := hy
  have hb := markedLens_bounds v hv edge width p
  have hr : 0 < markedLensRadius v edge width p := markedLensRadius_pos v edge width p
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    inner_smul_right, abs_mul, abs_of_pos hr] at hb
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht,
    inner_smul_right, abs_mul, abs_of_nonneg ht]
  constructor
  · exact (mul_le_mul_of_nonneg_right htr (norm_nonneg _)).trans hb.1
  · exact (mul_le_mul_of_nonneg_right htr (abs_nonneg _)).trans hb.2





theorem exists_transported_marked_lens
    {v : E3} (hv : ‖v‖ = 1) (c s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (γ : S1 → Hemisphere.Plane v)
    (hboundary : A '' sphere (0 : Hemisphere.Plane v) 1 = range γ)
    (g : E2 → E3)
    (hcore : g '' closedBall (0 : E2) 1 =
      liftPlaneDiffeomorph hv c s hs A ''
        ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
          {p : S2 | 0 ≤ inner Real v (p : E3)}))
    {η R width : Real} (hR : 1 < R) (hR' : R ≤ 5 / 4) (hRη : R - 1 < η)
    (hw : 0 < width)
    (hcollar : ∀ p : S1, ∀ r : Real, |r - 1| < η →
      g (r • (p : E2)) = (c + s * capCollarClock r) • v + (γ p : E3)) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      g '' closedBall (0 : E2) R ⊆ F '' sphere (0 : E3) 1 ∧
      (∀ y ∈ (F '' sphere (0 : E3) 1) \ (g '' closedBall (0 : E2) R),
        (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' ball 0 1) ∧
      (∀ y ∈ F '' closedBall (0 : E3) 1,
        (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' closedBall 0 1 ∧
        |inner Real v y - c| ≤ 2 * |s|) ∧
      (∀ p : S2, F p = liftPlaneDiffeomorph hv c s hs A
        (markedLensRadius v (capCollarClock R) width p • (p : E3))) := by
  let T := liftPlaneDiffeomorph hv c s hs A
  let M := (fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
    {p : S2 | capCollarClock R ≤ inner Real v (boundedCylinderRadius v p • (p : E3))}
  obtain ⟨B, hB, hmarked, hstrict, _, hbody⟩ :=
    exists_ambient_marked_lens v hv (capCollarClock R) hw
  have hM : M ⊆ B '' sphere (0 : E3) 1 :=
    inter_eq_right.mp hmarked
  have hmark : g '' closedBall (0 : E2) R = T '' M :=
    image_extended_cap_eq_truncated_model hv c s hs A γ hboundary g hcore hR hR' hRη hcollar
  let F := B.trans T
  have hFsphere : F '' sphere (0 : E3) 1 = T '' (B '' sphere (0 : E3) 1) :=
    image_comp T B _
  have hFbody : F '' closedBall (0 : E3) 1 =
      T '' Poincare.Topology.radialClosedBody (markedLensRadius v (capCollarClock R) width) := by
    change (T ∘ B) '' closedBall (0 : E3) 1 = _
    rw [image_comp, hbody]
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · rw [hmark, hFsphere]
    exact image_mono hM
  · rintro y ⟨hy, hynot⟩
    rw [hFsphere] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hznot : z ∉ M := fun hm => hynot (hmark.symm ▸ mem_image_of_mem T hm)
    have hzlt := hstrict z ⟨hz, hznot⟩
    change (Hemisphere.Plane v).orthogonalProjectionOnto
      (liftPlaneDiffeomorph hv c s hs A z) ∈ _
    rw [projection_liftPlaneDiffeomorph]
    exact mem_image_of_mem A (mem_ball_zero_iff.mpr hzlt)
  · intro y hy
    rw [hFbody] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hzbound := radialBody_markedLens_bounds v hv (capCollarClock R) width hz
    change (Hemisphere.Plane v).orthogonalProjectionOnto
      (liftPlaneDiffeomorph hv c s hs A z) ∈ _ ∧ _
    rw [projection_liftPlaneDiffeomorph]
    refine ⟨mem_image_of_mem A (mem_closedBall_zero_iff.mpr hzbound.1), ?_⟩
    change |inner Real v (liftPlaneDiffeomorph hv c s hs A z) - c| ≤ _
    rw [inner_liftPlaneDiffeomorph, add_sub_cancel_left, abs_mul]
    nlinarith [abs_nonneg s]
  · intro p
    change T (B p) = _
    rw [hB]



theorem lens_inter_replacement_eq_marked_disk
    {v : E3} (c s : Real)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (g : E2 → E3) {R : Real} (hR : 1 ≤ R) (retained : Set E3)
    (hmark : g '' closedBall (0 : E2) R ⊆ F '' sphere (0 : E3) 1)
    (hmarkedSurface : g '' closedBall (0 : E2) R ⊆
      (g '' closedBall (0 : E2) 1) ∪ retained)
    (hstrict : ∀ y ∈ (F '' sphere (0 : E3) 1) \ (g '' closedBall (0 : E2) R),
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' ball 0 1)
    (hbound : ∀ y ∈ F '' closedBall (0 : E3) 1,
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' closedBall 0 1 ∧
      |inner Real v y - c| ≤ 2 * |s|)
    (hclear : ∀ y ∈ retained,
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' closedBall 0 1 →
      |inner Real v y - c| ≤ 2 * |s| →
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' sphere 0 1) :
    (F '' sphere (0 : E3) 1) ∩ ((g '' closedBall (0 : E2) 1) ∪ retained) =
      g '' closedBall (0 : E2) R := by
  apply Subset.antisymm
  · rintro y ⟨hyF, hyg | hyr⟩
    · exact image_mono (closedBall_subset_closedBall hR) hyg
    · by_contra hn
      have hpball := hstrict y ⟨hyF, hn⟩
      have hbounds := hbound y (image_mono sphere_subset_closedBall hyF)
      have hpsphere := hclear y hyr hbounds.1 hbounds.2
      obtain ⟨x, hx, hxy⟩ := hpball
      obtain ⟨z, hz, hzy⟩ := hpsphere
      have hxz := A.injective (hxy.trans hzy.symm)
      subst z
      exact (ne_of_lt (mem_ball_zero_iff.mp hx)) (mem_sphere_zero_iff_norm.mp hz)
  · intro y hy
    exact ⟨hmark hy, hmarkedSurface hy⟩

end Poincare.Manifold.Schoenflies.Reverse
