import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Disk
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Side

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1

structure CircleFamily (a b : Real) where
  hab : a ≤ b
  map : Real × S1 → E2
  smooth : ContMDiff (𝓘(Real, Real).prod (𝓡 1)) (𝓡 2) ∞ map
  embedding : ∀ t ∈ Icc a b,
    _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞
      (fun p : S1 => map (t, p))

namespace CircleFamily

variable {a b : Real} (A : CircleFamily a b)

private theorem image_transport
    (Phi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {B : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞}
    (hB : B '' sphere (0 : E2) 1 = range (fun p : S1 => A.map (a, p)))
    (hmotion : ∀ t ∈ Icc a b, ∀ p : S1,
      Phi t (A.map (a, p)) = A.map (t, p))
    (t : Real) (ht : t ∈ Icc a b) :
    B.trans (Phi t) '' sphere (0 : E2) 1 = range (fun p : S1 => A.map (t, p)) := by
  rw [Diffeomorph.coe_trans, image_comp, hB]
  ext y
  constructor
  · rintro ⟨x, ⟨p, rfl⟩, rfl⟩
    exact ⟨p, (hmotion t ht p).symm⟩
  · rintro ⟨p, rfl⟩
    exact ⟨A.map (a, p), ⟨p, rfl⟩, hmotion t ht p⟩

private theorem frontier_transport
    (Phi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {B : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞}
    {hB : frontier (B '' closedBall (0 : E2) 1) =
      range (fun p : S1 => A.map (a, p))}
    (hmotion : ∀ t ∈ Icc a b, ∀ p : S1,
      Phi t (A.map (a, p)) = A.map (t, p))
    (t : Real) (ht : t ∈ Icc a b) :
    frontier (B.trans (Phi t) '' closedBall (0 : E2) 1) =
      range (fun p : S1 => A.map (t, p)) := by
  have hset : B.trans (Phi t) '' closedBall (0 : E2) 1 =
      Phi t '' (B '' closedBall (0 : E2) 1) := by
    rw [Diffeomorph.coe_trans, image_image]
    rfl
  calc
    frontier (B.trans (Phi t) '' closedBall (0 : E2) 1) =
        frontier (Phi t '' (B '' closedBall (0 : E2) 1)) := congrArg frontier hset
    _ = Phi t '' frontier (B '' closedBall (0 : E2) 1) :=
      (Phi t).toHomeomorph.image_frontier _ |>.symm
    _ = Phi t '' range (fun p : S1 => A.map (a, p)) := congrArg (fun K => Phi t '' K) hB
    _ = range (fun p : S1 => A.map (t, p)) := by
      ext y
      constructor
      · rintro ⟨x, ⟨p, rfl⟩, rfl⟩
        exact ⟨p, (hmotion t ht p).symm⟩
      · rintro ⟨p, rfl⟩
        exact ⟨A.map (a, p), ⟨p, rfl⟩, hmotion t ht p⟩

theorem exists_disk_family :
    ∃ C : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      ContDiff Real ∞ (fun z : Real × E2 => C z.1 z.2) ∧
      (∀ t ∈ Icc a b, C t '' sphere (0 : E2) 1 =
        range (fun p : S1 => A.map (t, p))) ∧
      (∀ t ∈ Icc a b, frontier (C t '' closedBall (0 : E2) 1) =
        range (fun p : S1 => A.map (t, p))) := by
  obtain ⟨B, hBsphere, _, hBfrontier, _⟩ :=
    exists_smooth_disk_of_smooth_circle (fun p : S1 => A.map (a, p))
      (A.embedding a ⟨le_rfl, A.hab⟩)
  obtain ⟨Phi, hPhi0, hPhi, _, hmotion⟩ :=
    Poincare.Manifold.Schoenflies.exists_ambient_isotopy_of_circle_isotopy
      A.hab A.map A.smooth A.embedding
  let C : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ := fun t => B.trans (Phi t)
  have hC : ContDiff Real ∞ (fun z : Real × E2 => C z.1 z.2) := by
    change ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 (B z.2))
    exact hPhi.comp (contDiff_fst.prodMk (B.contDiff.comp contDiff_snd))
  refine ⟨C, hC, ?_, ?_⟩
  · intro t ht
    exact image_transport A Phi hBsphere hmotion t ht
  · intro t ht
    exact frontier_transport A Phi (hB := hBfrontier) hmotion t ht

end CircleFamily

end Poincare.Manifold.Schoenflies.Saddle.Wall.Side
