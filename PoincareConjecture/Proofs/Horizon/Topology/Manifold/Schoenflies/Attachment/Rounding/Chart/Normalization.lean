import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.MarkedBall












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Rounding.Normalization

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1



theorem exists_ambient_ball_normalization
    (b : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (g : E2 → S2)
    (hgi : InjOn g (closedBall 0 1))
    (hgl : ∀ x ∈ closedBall (0 : E2) 1,
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ g x) :
    ∃ J : E2 ≃ₗᵢ[Real] Hemisphere.Plane (g 0 : E3),
      ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        H '' (b '' closedBall 0 1) = closedBall 0 1 ∧
        H '' (b '' ball 0 1) = ball 0 1 ∧
        H '' (b '' sphere 0 1) = sphere 0 1 ∧
        (∀ x ∈ closedBall (0 : E2) 1,
          H (b (g x)) = (Hemisphere.toSphere (norm_eq_of_mem_sphere (g 0)) (J x) : E3)) ∧
        H '' ((fun x => b (g x)) '' closedBall (0 : E2) 1) =
          (fun y => (Hemisphere.toSphere (norm_eq_of_mem_sphere (g 0)) y : E3)) ''
            closedBall (0 : Hemisphere.Plane (g 0 : E3)) 1 ∧
        H '' ((fun x => b (g x)) '' ball (0 : E2) 1) =
          (fun y => (Hemisphere.toSphere (norm_eq_of_mem_sphere (g 0)) y : E3)) ''
            ball (0 : Hemisphere.Plane (g 0 : E3)) 1 ∧
        H '' ((fun x => b (g x)) '' sphere (0 : E2) 1) =
          (fun y => (Hemisphere.toSphere (norm_eq_of_mem_sphere (g 0)) y : E3)) ''
            sphere (0 : Hemisphere.Plane (g 0 : E3)) 1 := by
  obtain ⟨J, N, hNball, hNdisk⟩ :=
    exists_marked_disk_round_coordinates zero_lt_one g hgi hgl
  let H := b.symm.trans N
  have hHb (x : E3) : H (b x) = N x := by
    change N (b.symm (b x)) = N x
    rw [b.symm_apply_apply]
  have hHball : H '' (b '' closedBall (0 : E3) 1) = closedBall 0 1 := by
    rw [image_image]
    calc
      (fun x => H (b x)) '' closedBall (0 : E3) 1 = N '' closedBall 0 1 :=
        image_congr (fun x _ => hHb x)
      _ = closedBall 0 1 := hNball
  have hHopen : H '' (b '' ball (0 : E3) 1) = ball 0 1 := by
    have h := congrArg interior hHball
    change interior (H.toHomeomorph '' (b.toHomeomorph '' closedBall (0 : E3) 1)) =
      interior (closedBall (0 : E3) 1) at h
    rw [← H.toHomeomorph.image_interior, ← b.toHomeomorph.image_interior,
      interior_closedBall (0 : E3) one_ne_zero] at h
    exact h
  have hHsphere : H '' (b '' sphere (0 : E3) 1) = sphere 0 1 := by
    have h := congrArg frontier hHball
    change frontier (H.toHomeomorph '' (b.toHomeomorph '' closedBall (0 : E3) 1)) =
      frontier (closedBall (0 : E3) 1) at h
    rw [← H.toHomeomorph.image_frontier, ← b.toHomeomorph.image_frontier,
      frontier_closedBall (0 : E3) one_ne_zero] at h
    exact h
  have hHdisk (x : E2) (hx : x ∈ closedBall 0 1) :
      H (b (g x)) = (Hemisphere.toSphere (norm_eq_of_mem_sphere (g 0)) (J x) : E3) := by
    rw [hHb]
    exact hNdisk x hx
  have himage (s : Set E2) (hs : s ⊆ closedBall 0 1) :
      H '' ((fun x => b (g x)) '' s) =
        (fun y => (Hemisphere.toSphere (norm_eq_of_mem_sphere (g 0)) y : E3)) '' (J '' s) := by
    rw [image_image, image_image]
    exact image_congr (fun x hx => hHdisk x (hs hx))
  refine ⟨J, H, hHball, hHopen, hHsphere, hHdisk, ?_, ?_, ?_⟩
  · rw [himage _ Subset.rfl, J.image_closedBall]
    simp only [map_zero]
  · rw [himage _ ball_subset_closedBall, J.image_ball]
    simp only [map_zero]
  · rw [himage _ sphere_subset_closedBall, J.image_sphere]
    simp only [map_zero]

end Poincare.Manifold.Schoenflies.Rounding.Normalization
