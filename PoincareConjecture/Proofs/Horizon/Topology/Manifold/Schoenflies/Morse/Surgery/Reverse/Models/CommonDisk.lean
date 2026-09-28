import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.Models.UnitLens



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




theorem exists_common_marked_unit_cap_lens
    {v : E3} (hv : ‖v‖ = 1) (c s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (g : E2 → E3) (hg : ContDiff Real ∞ g) (hgi : Injective g)
    (hgder : ∀ x, Injective (fderiv Real g x))
    (hcore : g '' closedBall (0 : E2) 1 =
      liftPlaneDiffeomorph hv c s hs A ''
        ((fun p : S2 => boundedCylinderRadius v p • (p : E3)) ''
          {p : S2 | 0 ≤ inner Real v (p : E3)}))
    {f : S2 → E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hboundary : B '' sphere (0 : E3) 1 = range f)
    (d : OpenPartialHomeomorph E2 S2)
    (hd : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d d.source)
    (hdi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ d.symm d.target)
    (hsource : closedBall (0 : E2) 1 ⊆ d.source)
    (hpatch : ∀ x ∈ closedBall (0 : E2) 1, f (d x) = g x)
    (retained : Set E3)
    (hrange : range f = (g '' closedBall (0 : E2) 1) ∪ retained)
    (hclear : ∀ y ∈ retained,
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' closedBall 0 1 →
      |inner Real v y - c| ≤ 2 * |s| →
      (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' sphere 0 1) :
    ∃ (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (m n : E2 → S2),
      InjOn m (closedBall 0 1) ∧ InjOn n (closedBall 0 1) ∧
      (∀ x ∈ closedBall (0 : E2) 1,
        IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ m x) ∧
      (∀ x ∈ closedBall (0 : E2) 1,
        IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ n x) ∧
      (∀ x ∈ closedBall (0 : E2) 1, B (m x : E3) = g x ∧ F (n x : E3) = g x) ∧
      (B '' sphere (0 : E3) 1) ∩ (F '' sphere (0 : E3) 1) =
        (fun x => B (m x : E3)) '' closedBall (0 : E2) 1 ∧
      (fun x => B (m x : E3)) '' closedBall (0 : E2) 1 =
        g '' closedBall (0 : E2) 1 ∧
      (fun x => B (m x : E3)) '' sphere (0 : E2) 1 =
        g '' sphere (0 : E2) 1 ∧
      (∀ y ∈ (F '' sphere (0 : E3) 1) \ (g '' closedBall (0 : E2) 1),
        (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' ball 0 1) ∧
      (∀ y ∈ F '' closedBall (0 : E3) 1,
        (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' closedBall 0 1 ∧
        |inner Real v y - c| ≤ 2 * |s|) := by
  obtain ⟨F, n, hni, hnl, hn, hnclosed, _, hstrict, hbound⟩ :=
    exists_parametrized_unit_cap_lens hv c s hs A g hg hgi hgder hcore
      (width := 1) (by norm_num)
  obtain ⟨m, hmi, hml, hm, hmclosed, hmedge⟩ :=
    exists_marked_cap_of_filling hf B hboundary d hd hdi hsource g hpatch
  have hmark : g '' closedBall (0 : E2) 1 ⊆ F '' sphere (0 : E3) 1 := by
    rw [← hnclosed]
    rintro y ⟨x, _, rfl⟩
    exact mem_image_of_mem F (n x).property
  have hmeet := lens_inter_replacement_eq_marked_disk c s A F g (R := 1) le_rfl retained
    hmark subset_union_left hstrict hbound hclear
  have hmeet' : (B '' sphere (0 : E3) 1) ∩ (F '' sphere (0 : E3) 1) =
      (fun x => B (m x : E3)) '' closedBall (0 : E2) 1 := by
    rw [hmclosed, hboundary, hrange, inter_comm]
    exact hmeet
  exact ⟨F, m, n, hmi, hni, hml, hnl, fun x hx => ⟨hm x hx, hn x hx⟩,
    hmeet', hmclosed, hmedge, hstrict, hbound⟩

end Poincare.Manifold.Schoenflies.Reverse
