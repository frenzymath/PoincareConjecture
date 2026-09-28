import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.CirclePair.AttachmentGerm.Restriction
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.CirclePair.AttachmentGerm.Side
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.Reparametrization

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.CircleAttachmentGerm

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private instance : Fact (Module.finrank Real E2 = 1 + 1) := ⟨by simp⟩

theorem exists_disk_diffeomorph_of_boundary_germ
    (P : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (p : S1)
    (hp : (p : E2) ∈ P.source)
    (hboundary : ∀ᶠ x in 𝓝 (p : E2), x ∈ sphere (0 : E2) 1 → P x ∈ sphere (0 : E2) 1)
    (hinside : ∀ᶠ t in 𝓝[<] (0 : Real), ‖P ((1 + t) • (p : E2))‖ < 1) :
    ∃ G : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      G '' closedBall (0 : E2) 1 = closedBall (0 : E2) 1 ∧
      G '' ball (0 : E2) 1 = ball (0 : E2) 1 ∧
      (G : E2 → E2) =ᶠ[𝓝 (p : E2)] P := by
  obtain ⟨f, hf, hfval⟩ := exists_circle_restriction_of_boundary_germ P p hp hboundary
  obtain ⟨q, hq⟩ := exists_circle_diffeomorph_of_local_germ f p hf
  obtain ⟨H, hHq, hHc, hHb⟩ := exists_ambient_diffeomorph_of_circle_diffeomorph q
  have hcircle : ∀ᶠ z : S1 in 𝓝 p, H (z : E2) = P z := by
    filter_upwards [hq, hfval] with z hqz hfz
    rw [hHq, hqz, hfz]
  have hlocal : ∀ᶠ x in 𝓝 (p : E2), x ∈ sphere (0 : E2) 1 → H x = P x :=
    eventually_nhdsWithin_iff.mp
      ((eventually_nhds_subtype_iff (sphere (0 : E2) 1) p (fun x => H x = P x)).mp hcircle)
  let k : E2 → E2 := fun x => H.symm (P x)
  have hksmooth : ContDiffOn Real ∞ k P.source := by
    exact H.symm.contMDiff.contDiff.comp_contDiffOn P.contMDiffOn.contDiffOn
  have hkfix : ∀ᶠ x in 𝓝 (p : E2), x ∈ sphere (0 : E2) 1 → k x = x := by
    filter_upwards [hlocal] with x hx
    intro hs
    change H.symm (P x) = x
    rw [← hx hs, H.symm_apply_apply]
  have hP : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ P (p : E2) :=
    ⟨P, hp, eqOn_refl _ _⟩
  have hkloc : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ k (p : E2) :=
    IsLocalDiffeomorphAt.comp (I := 𝓡 2) (J := 𝓡 2) (K := 𝓡 2) (P := E2) (n := ∞)
      hP (H.symm.isLocalDiffeomorph (P p))
  have hkinj : Injective (fderiv Real k p) := by
    rw [← mfderiv_eq_fderiv]
    exact (hkloc.mfderivToContinuousLinearEquiv (by simp)).injective
  have hkinside : ∀ᶠ t in 𝓝[<] (0 : Real), ‖k ((1 + t) • (p : E2))‖ < 1 := by
    filter_upwards [hinside] with t ht
    have hPball : P ((1 + t) • (p : E2)) ∈ H '' ball (0 : E2) 1 := by
      rw [hHb]
      simpa only [mem_ball, dist_zero_right] using ht
    obtain ⟨x, hx, heq⟩ := hPball
    change ‖H.symm (P ((1 + t) • (p : E2)))‖ < 1
    rw [← heq, H.symm_apply_apply]
    simpa only [mem_ball, dist_zero_right] using hx
  obtain ⟨G, hGc, hGb, _, hGerm⟩ := exists_disk_diffeomorph_of_local_inward_germ
    k p P.open_source hp hksmooth hkfix hkinj hkinside
  refine ⟨G.trans H, ?_, ?_, ?_⟩
  · change (H ∘ G) '' closedBall (0 : E2) 1 = _
    rw [image_comp, hGc, hHc]
  · change (H ∘ G) '' ball (0 : E2) 1 = _
    rw [image_comp, hGb, hHb]
  · filter_upwards [hGerm] with x hx
    change H (G x) = P x
    rw [hx]
    exact H.apply_symm_apply (P x)

end Poincare.Manifold.Schoenflies.CircleAttachmentGerm
