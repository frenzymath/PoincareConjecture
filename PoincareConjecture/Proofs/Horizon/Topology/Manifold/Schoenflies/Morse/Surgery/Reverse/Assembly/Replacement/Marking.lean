import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Models.ClosedMarking



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Reverse

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1



theorem exists_ambient_disk_marking
    (B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (g : E2 → E3) (hg : ContDiff Real ∞ g)
    (hgi : InjOn g (closedBall (0 : E2) 1))
    (hgd : ∀ x ∈ closedBall (0 : E2) 1, Injective (fderiv Real g x))
    (hsub : g '' closedBall (0 : E2) 1 ⊆ B '' sphere (0 : E3) 1)
    (p0 : S2) :
    ∃ m : E2 → S2, InjOn m (closedBall 0 1) ∧
      (∀ x ∈ closedBall (0 : E2) 1,
        IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ m x) ∧
      ∀ x ∈ closedBall (0 : E2) 1, B (m x : E3) = g x := by
  let G : E2 → E3 := B.symm ∘ g
  have hG : ContDiff Real ∞ G := B.symm.contDiff.comp hg
  have hGi : InjOn G (closedBall (0 : E2) 1) := by
    intro x hx y hy heq
    exact hgi hx hy (B.symm.injective heq)
  have hGd (x : E2) (hx : x ∈ closedBall (0 : E2) 1) :
      Injective (fderiv Real G x) := by
    have hBd : Injective (fderiv Real B.symm (g x)) := by
      have h := (B.symm.mfderivToContinuousLinearEquiv (by simp) (g x)).injective
      change Injective (mfderiv (𝓡 3) (𝓡 3) B.symm (g x)) at h
      simpa only [mfderiv_eq_fderiv, TangentSpace] using h
    rw [show G = B.symm ∘ g from rfl, fderiv_comp x
      (B.symm.contDiff.differentiable (by simp) _) (hg.differentiable (by simp) x)]
    exact hBd.comp (hgd x hx)
  have hmem (x : E2) (hx : x ∈ closedBall (0 : E2) 1) : G x ∈ sphere (0 : E3) 1 := by
    obtain ⟨z, hz, heq⟩ := hsub (mem_image_of_mem g hx)
    change B.symm (g x) ∈ _
    rw [← heq, B.symm_apply_apply]
    exact hz
  obtain ⟨m, hm, hmi, hml⟩ := exists_spherical_marking_on_closedBall G hG hGi hGd hmem p0
  refine ⟨m, hmi, hml, ?_⟩
  intro x hx
  rw [hm x hx]
  exact B.apply_symm_apply (g x)


theorem exists_ambient_disk_marking_at_radius
    (B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (g : E2 → E3) (hg : ContDiff Real ∞ g) (hgi : Injective g)
    (hgd : ∀ x, Injective (fderiv Real g x))
    {r : Real} (hr : 0 < r)
    (hsub : g '' closedBall (0 : E2) r ⊆ B '' sphere (0 : E3) 1)
    (p0 : S2) :
    ∃ m : E2 → S2, InjOn m (closedBall 0 1) ∧
      (∀ x ∈ closedBall (0 : E2) 1,
        IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ m x) ∧
      (∀ x ∈ closedBall (0 : E2) 1, B (m x : E3) = g (r • x)) ∧
      (fun x => B (m x : E3)) '' closedBall (0 : E2) 1 =
        g '' closedBall (0 : E2) r := by
  let L : E2 ≃L[Real] E2 :=
    (LinearEquiv.smulOfNeZero Real E2 r hr.ne').toContinuousLinearEquiv
  have hLball : L '' closedBall (0 : E2) 1 = closedBall 0 r := by
    change (fun x : E2 => r • x) '' closedBall 0 1 = _
    rw [image_smul, _root_.smul_closedBall' hr.ne', smul_zero, Real.norm_eq_abs,
      abs_of_pos hr, mul_one]
  have hd (x : E2) : Injective (fderiv Real (g ∘ L) x) := by
    rw [fderiv_comp x (hg.differentiable (by simp) _) (L.differentiableAt),
      L.fderiv]
    exact (hgd (L x)).comp L.injective
  obtain ⟨m, hmi, hml, hm⟩ := exists_ambient_disk_marking B (g ∘ L)
    (hg.comp L.contDiff) (hgi.comp L.injective).injOn (fun x _ => hd x)
    (by rw [image_comp, hLball]; exact hsub) p0
  refine ⟨m, hmi, hml, hm, ?_⟩
  calc
    (fun x => B (m x : E3)) '' closedBall (0 : E2) 1 =
        (g ∘ L) '' closedBall (0 : E2) 1 := image_congr hm
    _ = g '' closedBall (0 : E2) r := by rw [image_comp, hLball]

end Poincare.Manifold.Schoenflies.Reverse
