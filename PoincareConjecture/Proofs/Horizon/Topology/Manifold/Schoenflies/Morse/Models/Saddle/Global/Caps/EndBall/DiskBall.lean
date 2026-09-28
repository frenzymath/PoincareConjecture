import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.Compression.MarkedBall
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Attachment.DiskComplement











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1



theorem exists_ball_along_sphere_disk_with_boundary_intersection
    {g : S2 → E3} (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (m : E2 → S2) (hmi : InjOn m (closedBall 0 1))
    (hml : ∀ x ∈ closedBall (0 : E2) 1,
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ m x)
    {W : Set E3} (hW : IsOpen W) (hDW : (g ∘ m) '' closedBall (0 : E2) 1 ⊆ W) :
    ∃ (B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (U : Set E3),
      IsOpen U ∧ (g ∘ m) '' closedBall (0 : E2) 1 ⊆ U ∧
      B '' closedBall (0 : E3) 1 ⊆ W ∧
      (B '' sphere (0 : E3) 1) ∩ U = range g ∩ U ∧
      (∀ x ∈ closedBall (0 : E2) 1, B (m x) = g (m x)) ∧
      (B '' closedBall (0 : E3) 1) ∩ range g ⊆ B '' sphere (0 : E3) 1 := by
  obtain ⟨e, hes, _, he, hei, heq⟩ := exists_sphere_neighborhood g hg
  let V := e.source ∩ e ⁻¹' W
  have hV : IsOpen V := e.continuousOn.isOpen_inter_preimage e.open_source hW
  have hDV : (fun x => (m x : E3)) '' closedBall (0 : E2) 1 ⊆ V := by
    rintro p ⟨x, hx, rfl⟩
    exact ⟨hes (m x).property, by
      change e (m x) ∈ W
      rw [heq]
      exact hDW (mem_image_of_mem _ hx)⟩
  obtain ⟨K, hK, _, hKD, F, hFfix, hFsmall⟩ :=
    Rounding.exists_marked_ball_compression (Diffeomorph.refl (𝓡 3) E3 ∞)
      m hmi hml V univ hV isOpen_univ hDV (subset_univ _)
  have hFs (x : E3) (hx : x ∈ closedBall 0 1) : F x ∈ e.source :=
    (hFsmall (mem_image_of_mem F (mem_image_of_mem _ hx))).2.1
  let ep : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ :=
    { e with contMDiffOn_toFun := he, contMDiffOn_invFun := hei }
  obtain ⟨B, hB⟩ := exists_global_extension_of_local_ball_embedding zero_lt_one (e ∘ F)
    (fun x hx y hy heq => F.injective (e.injOn (hFs x hx) (hFs y hy) heq))
    (fun x hx => (F.isLocalDiffeomorph x).comp (𝓡 3) E3
      (ep.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (hFs x hx)))
  let U := e '' (e.source ∩ Kᶜ)
  have hFmark (x : E2) (hx : x ∈ closedBall 0 1) : F (m x) = m x :=
    hFfix _ (fun hp => disjoint_left.mp hKD hp (mem_image_of_mem _ hx))
  have hFclosed : F '' closedBall (0 : E3) 1 ⊆ closedBall (0 : E3) 1 := by
    have h := hFsmall
    simp only [Diffeomorph.coe_refl, image_id] at h
    exact h.trans inter_subset_left
  have hFball : F '' ball (0 : E3) 1 ⊆ ball (0 : E3) 1 := by
    have h := interior_mono hFclosed
    change interior (F.toHomeomorph '' closedBall (0 : E3) 1) ⊆
      interior (closedBall (0 : E3) 1) at h
    rw [← F.toHomeomorph.image_interior,
      interior_closedBall (0 : E3) (by norm_num : (1 : Real) ≠ 0)] at h
    exact h
  refine ⟨B, U, e.isOpen_image_of_subset_source
    (e.open_source.inter hK.isClosed.isOpen_compl) inter_subset_left, ?_, ?_, ?_, ?_, ?_⟩
  · rintro p ⟨x, hx, rfl⟩
    exact ⟨m x, ⟨hes (m x).property,
      fun hp => disjoint_left.mp hKD hp (mem_image_of_mem _ hx)⟩, heq (m x)⟩
  · rintro p ⟨x, hx, rfl⟩
    rw [hB x hx]
    exact (hFsmall (mem_image_of_mem F (mem_image_of_mem _ hx))).2.2
  · ext y
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hyU⟩
      obtain ⟨z, ⟨hzs, hzK⟩, hz⟩ := hyU
      have hBx : B x = e (F x) := hB x (sphere_subset_closedBall hx)
      have hzFx : z = F x := e.injOn hzs (hFs x (sphere_subset_closedBall hx)) (hz.trans hBx)
      have hzx : z = x := F.injective ((hFfix z hzK).trans hzFx)
      have hyU' : B x ∈ U := ⟨z, ⟨hzs, hzK⟩, hz⟩
      refine ⟨⟨⟨x, hx⟩, ?_⟩, hyU'⟩
      exact (heq ⟨x, hx⟩).symm.trans ((congrArg e hzx.symm).trans hz)
    · rintro ⟨⟨p, rfl⟩, hpU⟩
      obtain ⟨z, ⟨hzs, hzK⟩, hz⟩ := hpU
      have hzp : z = p := e.injOn hzs (hes p.property) (hz.trans (heq p).symm)
      have hpK : (p : E3) ∉ K := hzp ▸ hzK
      refine ⟨⟨p, p.property, ?_⟩, ⟨z, ⟨hzs, hzK⟩, hz⟩⟩
      rw [hB p (sphere_subset_closedBall p.property)]
      change e (F p) = g p
      rw [hFfix p hpK, heq]
  · intro x hx
    rw [hB (m x) (sphere_subset_closedBall (m x).property)]
    change e (F (m x)) = g (m x)
    rw [hFmark x hx, heq]
  · rintro y ⟨⟨x, hx, rfl⟩, p, hp⟩
    have hFp : F x = (p : E3) :=
      e.injOn (hFs x hx) (hes p.property) ((hB x hx).symm.trans (hp.symm.trans (heq p).symm))
    have hxnot : x ∉ ball (0 : E3) 1 := by
      intro hxb
      have hpball := hFball (mem_image_of_mem F hxb)
      rw [hFp] at hpball
      exact (not_lt_of_ge (le_of_eq (mem_sphere.mp p.property).symm)) (mem_ball.mp hpball)
    exact ⟨x, by rw [← closedBall_sdiff_ball]; exact ⟨hx, hxnot⟩, rfl⟩



theorem exists_ball_along_sphere_disk
    {g : S2 → E3} (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (m : E2 → S2) (hmi : InjOn m (closedBall 0 1))
    (hml : ∀ x ∈ closedBall (0 : E2) 1,
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ m x)
    {W : Set E3} (hW : IsOpen W) (hDW : (g ∘ m) '' closedBall (0 : E2) 1 ⊆ W) :
    ∃ (B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (U : Set E3),
      IsOpen U ∧ (g ∘ m) '' closedBall (0 : E2) 1 ⊆ U ∧
      B '' closedBall (0 : E3) 1 ⊆ W ∧
      (B '' sphere (0 : E3) 1) ∩ U = range g ∩ U ∧
      ∀ x ∈ closedBall (0 : E2) 1, B (m x) = g (m x) := by
  obtain ⟨B, U, hU, hDU, hBW, hBU, hBm, _⟩ :=
    exists_ball_along_sphere_disk_with_boundary_intersection hg m hmi hml hW hDW
  exact ⟨B, U, hU, hDU, hBW, hBU, hBm⟩

end Poincare.Manifold.Schoenflies.Saddle.Caps
