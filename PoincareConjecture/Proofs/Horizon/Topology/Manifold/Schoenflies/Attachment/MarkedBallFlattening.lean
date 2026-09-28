import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.MarkedBall
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.FlatMarkedBall

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem exists_marked_ball_flattening
    (g : E3 → E3) (hginj : InjOn g (closedBall 0 1))
    (hgloc : ∀ y ∈ closedBall (0 : E3) 1,
      IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ g y)
    {r : Real} (hr : 0 < r) (f : E2 → S2)
    (hfinj : InjOn f (closedBall 0 r))
    (hfloc : ∀ x ∈ closedBall (0 : E2) r,
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ f x) :
    ∃ J : E2 ≃ₗᵢ[Real] Hemisphere.Plane (f 0 : E3),
      ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ x : E2, ‖x‖ ≤ r → H (g (f x)) = (J x : E3) + (f 0 : E3)) ∧
        (H '' (g '' closedBall (0 : E3) 1)) ∩ unitBallMarkedCone (f 0) r =
          {y | y ∈ unitBallMarkedCone (f 0) r ∧ inner Real (f 0 : E3) y ≤ 1} := by
  obtain ⟨G, hG⟩ := exists_global_extension_of_local_ball_embedding
    zero_lt_one g hginj hgloc
  obtain ⟨J, N, hNball, hN⟩ := exists_marked_disk_round_coordinates hr f hfinj hfloc
  obtain ⟨_, _, _, P, _, hPdisk, hPside⟩ :=
    exists_flat_marked_unitBall (norm_eq_of_mem_sphere (f 0)) hr
  let H := (G.symm.trans N).trans P
  have hGball : g '' closedBall (0 : E3) 1 = G '' closedBall (0 : E3) 1 :=
    image_congr (fun y hy => (hG y hy).symm)
  have hHball : H '' (g '' closedBall (0 : E3) 1) = P '' closedBall (0 : E3) 1 := by
    calc
      H '' (g '' closedBall (0 : E3) 1) =
          P '' (N '' (G.symm '' (g '' closedBall (0 : E3) 1))) := by
        simp only [image_image]
        rfl
      _ = P '' closedBall (0 : E3) 1 := by
        rw [hGball]
        have hcancel : G.symm '' (G '' closedBall (0 : E3) 1) = closedBall (0 : E3) 1 := by
          simp only [image_image, Diffeomorph.symm_apply_apply, image_id']
        rw [hcancel, hNball]
  refine ⟨J, H, ?_, ?_⟩
  · intro x hx
    have hxf : (f x : E3) ∈ closedBall (0 : E3) 1 :=
      sphere_subset_closedBall (f x).property
    have hxr : x ∈ closedBall (0 : E2) r := by simpa using hx
    change P (N (G.symm (g (f x)))) = _
    rw [← hG (f x) hxf, G.symm_apply_apply, hN x hxr]
    exact hPdisk (J x) (by simpa using hx)
  · rw [hHball]
    exact hPside

end Poincare.Manifold.Schoenflies
