import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Models.TransportedLens
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Models.ClosedMarking
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.MarkedDisks



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Reverse

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

open Poincare.Geometry.Euclidean




theorem exists_parametrized_unit_cap_lens
    {v : E3} (hv : ‖v‖ = 1) (c s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (g : E2 → E3) (hg : ContDiff Real ∞ g) (hgi : Injective g)
    (hgder : ∀ x, Injective (fderiv Real g x))
    (hcore : g '' closedBall (0 : E2) 1 =
      liftPlaneDiffeomorph hv c s hs A ''
        ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
          {p : S2 | 0 ≤ inner Real v (p : E3)}))
    {width : Real} (hw : 0 < width) :
    ∃ (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (m : E2 → S2),
      InjOn m (closedBall 0 1) ∧
      (∀ x ∈ closedBall (0 : E2) 1,
        IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ m x) ∧
      (∀ x ∈ closedBall (0 : E2) 1, F (m x : E3) = g x) ∧
      (fun x => F (m x : E3)) '' closedBall (0 : E2) 1 =
        g '' closedBall (0 : E2) 1 ∧
      (fun x => F (m x : E3)) '' sphere (0 : E2) 1 =
        g '' sphere (0 : E2) 1 ∧
      (∀ y ∈ (F '' sphere (0 : E3) 1) \ (g '' closedBall (0 : E2) 1),
        (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' ball 0 1) ∧
      (∀ y ∈ F '' closedBall (0 : E3) 1,
        (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' closedBall 0 1 ∧
        |inner Real v y - c| ≤ 2 * |s|) := by
  let T := liftPlaneDiffeomorph hv c s hs A
  let graph : S2 → E3 := fun p => boundedCylinderRadius v p • (p : E3)
  let M := graph '' {p : S2 | 0 ≤ inner Real v (graph p)}
  have hmarked : g '' closedBall (0 : E2) 1 = T '' M := by
    rw [hcore]
    congr 2
    ext p
    change (0 ≤ inner Real v (p : E3)) ↔ (0 ≤ inner Real v (graph p))
    change (0 ≤ inner Real v (p : E3)) ↔
      (0 ≤ inner Real v (boundedCylinderRadius v p • (p : E3)))
    rw [inner_smul_right]
    exact (mul_nonneg_iff_of_pos_left (boundedCylinderRadius_pos v p)).symm
  obtain ⟨L, hL, _, hstrict, _, hbody⟩ := exists_ambient_marked_lens v hv 0 hw
  let F := L.trans T
  have hFsphere : F '' sphere (0 : E3) 1 = T '' (L '' sphere (0 : E3) 1) := image_comp T L _
  have hFbody : F '' closedBall (0 : E3) 1 =
      T '' Poincare.Topology.radialClosedBody (markedLensRadius v 0 width) := by
    change (T ∘ L) '' closedBall (0 : E3) 1 = _
    rw [image_comp, hbody]
  obtain ⟨B, _, hB, _, _⟩ := exists_boundedCylinder_ambient v hv
  let H := T.symm.trans B.symm
  let G : E2 → E3 := H ∘ g
  have hG : ContDiff Real ∞ G := H.contDiff.comp hg
  have hGder (x : E2) : Injective (fderiv Real G x) := by
    have hHder : Injective (fderiv Real H (g x)) := by
      have h := (H.mfderivToContinuousLinearEquiv (by simp) (g x)).injective
      change Injective (mfderiv (𝓡 3) (𝓡 3) H (g x)) at h
      simpa only [mfderiv_eq_fderiv, TangentSpace] using h
    rw [show G = H ∘ g from rfl, fderiv_comp x
      (H.contDiff.differentiable (by simp) _) (hg.differentiable (by simp) x)]
    exact hHder.comp (hgder x)
  have hmem (x : E2) (hx : x ∈ closedBall (0 : E2) 1) : G x ∈ sphere (0 : E3) 1 := by
    have hh := hcore ▸ mem_image_of_mem g hx
    obtain ⟨z, ⟨p, _, rfl⟩, hp⟩ := hh
    have heq : G x = (p : E3) := by
      change B.symm (T.symm (g x)) = _
      rw [← hp, T.symm_apply_apply]
      change B.symm (boundedCylinderRadius v p • (p : E3)) = _
      rw [← hB p, B.symm_apply_apply]
    exact heq.symm ▸ p.property
  obtain ⟨m, hm, hmi, hml⟩ := exists_spherical_marking_on_closedBall G hG
    (H.injective.comp hgi).injOn (fun x _ => hGder x) hmem
    ⟨v, mem_sphere_zero_iff_norm.mpr hv⟩
  have hTm (x : E2) (hx : x ∈ closedBall (0 : E2) 1) : T (B (m x : E3)) = g x := by
    rw [hm x hx]
    change T (B (B.symm (T.symm (g x)))) = g x
    rw [B.apply_symm_apply, T.apply_symm_apply]
  have hFm (x : E2) (hx : x ∈ closedBall (0 : E2) 1) : F (m x : E3) = g x := by
    have hh := hmarked ▸ mem_image_of_mem g hx
    obtain ⟨z, ⟨p, hp, rfl⟩, hpg⟩ := hh
    have hpm : p = m x := by
      apply Subtype.ext
      apply B.injective
      apply T.injective
      change T (B (p : E3)) = T (B (m x : E3))
      rw [hB p]
      exact hpg.trans (hTm x hx).symm
    rw [← hpm]
    change T (L (p : E3)) = g x
    rw [hL p, markedLensRadius_eq_of_height_ge v 0 hw p hp]
    exact hpg
  refine ⟨F, m, hmi, hml, hFm, image_congr hFm,
    image_congr (fun x hx => hFm x (sphere_subset_closedBall hx)), ?_, ?_⟩
  · rintro y ⟨hy, hynot⟩
    rw [hFsphere] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hznot : z ∉ M := fun hm => hynot (hmarked.symm ▸ mem_image_of_mem T hm)
    have hzlt := hstrict z ⟨hz, hznot⟩
    change (Hemisphere.Plane v).orthogonalProjectionOnto
      (liftPlaneDiffeomorph hv c s hs A z) ∈ _
    rw [projection_liftPlaneDiffeomorph]
    exact mem_image_of_mem A (mem_ball_zero_iff.mpr hzlt)
  · intro y hy
    rw [hFbody] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hzbound := radialBody_markedLens_bounds v hv 0 width hz
    change (Hemisphere.Plane v).orthogonalProjectionOnto
      (liftPlaneDiffeomorph hv c s hs A z) ∈ _ ∧ _
    rw [projection_liftPlaneDiffeomorph]
    refine ⟨mem_image_of_mem A (mem_closedBall_zero_iff.mpr hzbound.1), ?_⟩
    change |inner Real v (liftPlaneDiffeomorph hv c s hs A z) - c| ≤ _
    rw [inner_liftPlaneDiffeomorph, add_sub_cancel_left, abs_mul]
    nlinarith [abs_nonneg s]

end Poincare.Manifold.Schoenflies.Reverse
