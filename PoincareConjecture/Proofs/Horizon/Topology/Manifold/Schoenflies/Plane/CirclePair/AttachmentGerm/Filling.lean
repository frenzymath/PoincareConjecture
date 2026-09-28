import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.CirclePair.AttachmentGerm.Extension
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Disk



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.CircleAttachmentGerm

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1



theorem exists_filling_with_boundary_germ
    (A : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (P : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (p : S1)
    (hp : (p : E2) ∈ P.source)
    (hboundary : ∀ᶠ x in 𝓝 (p : E2), x ∈ sphere (0 : E2) 1 →
      P x ∈ A '' sphere (0 : E2) 1)
    (hinside : ∀ᶠ t in 𝓝[<] (0 : Real),
      P ((1 + t) • (p : E2)) ∈ A '' ball (0 : E2) 1) :
    ∃ F : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      F '' closedBall (0 : E2) 1 = A '' closedBall (0 : E2) 1 ∧
      F '' ball (0 : E2) 1 = A '' ball (0 : E2) 1 ∧
      F '' sphere (0 : E2) 1 = A '' sphere (0 : E2) 1 ∧
      (F : E2 → E2) =ᶠ[𝓝 (p : E2)] P := by
  let Q := P.trans A.symm.toPartialDiffeomorph
  have hpQ : (p : E2) ∈ Q.source := ⟨hp, mem_univ _⟩
  have hQboundary : ∀ᶠ x in 𝓝 (p : E2), x ∈ sphere (0 : E2) 1 →
      Q x ∈ sphere (0 : E2) 1 := by
    filter_upwards [hboundary] with x hx
    intro hs
    obtain ⟨y, hy, hxy⟩ := hx hs
    change A.symm (P x) ∈ sphere (0 : E2) 1
    rwa [← hxy, A.symm_apply_apply]
  have hQinside : ∀ᶠ t in 𝓝[<] (0 : Real), ‖Q ((1 + t) • (p : E2))‖ < 1 := by
    filter_upwards [hinside] with t ht
    obtain ⟨y, hy, hty⟩ := ht
    change ‖A.symm (P ((1 + t) • (p : E2)))‖ < 1
    rw [← hty, A.symm_apply_apply]
    simpa only [mem_ball, dist_zero_right] using hy
  obtain ⟨G, hGc, hGb, hGerm⟩ :=
    exists_disk_diffeomorph_of_boundary_germ Q p hpQ hQboundary hQinside
  have hGs : G '' sphere (0 : E2) 1 = sphere (0 : E2) 1 := by
    have h := G.toHomeomorph.image_frontier (closedBall (0 : E2) 1)
    change G '' frontier (closedBall (0 : E2) 1) = frontier (G '' closedBall (0 : E2) 1) at h
    rw [frontier_closedBall _ (by norm_num : (1 : Real) ≠ 0), hGc,
      frontier_closedBall _ (by norm_num : (1 : Real) ≠ 0)] at h
    exact h
  refine ⟨G.trans A, ?_, ?_, ?_, ?_⟩
  · change (A ∘ G) '' closedBall (0 : E2) 1 = _
    rw [image_comp, hGc]
  · change (A ∘ G) '' ball (0 : E2) 1 = _
    rw [image_comp, hGb]
  · change (A ∘ G) '' sphere (0 : E2) 1 = _
    rw [image_comp, hGs]
  · filter_upwards [hGerm] with x hx
    change A (G x) = P x
    rw [hx]
    exact A.apply_symm_apply (P x)



theorem exists_smooth_circle_filling_realizing_boundary_germs
    (f : S1 → E2) (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ f) :
    ∃ A : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      A '' sphere (0 : E2) 1 = range f ∧
      ∀ (P : PartialDiffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞) (p : S1),
        (p : E2) ∈ P.source →
        (∀ᶠ x in 𝓝 (p : E2), x ∈ sphere (0 : E2) 1 → P x ∈ range f) →
        (∀ᶠ t in 𝓝[<] (0 : Real), P ((1 + t) • (p : E2)) ∈ A '' ball (0 : E2) 1) →
        ∃ F : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
          F '' closedBall (0 : E2) 1 = A '' closedBall (0 : E2) 1 ∧
          F '' ball (0 : E2) 1 = A '' ball (0 : E2) 1 ∧
          F '' sphere (0 : E2) 1 = range f ∧
          (F : E2 → E2) =ᶠ[𝓝 (p : E2)] P := by
  obtain ⟨A, hA⟩ := exists_ambient_diffeomorph_of_smooth_circle f hf
  refine ⟨A, hA, ?_⟩
  intro P p hp hboundary hinside
  obtain ⟨F, hFc, hFb, hFs, hFerm⟩ := exists_filling_with_boundary_germ A P p hp
    (by simpa only [hA] using hboundary) hinside
  exact ⟨F, hFc, hFb, hFs.trans hA, hFerm⟩

end Poincare.Manifold.Schoenflies.CircleAttachmentGerm
