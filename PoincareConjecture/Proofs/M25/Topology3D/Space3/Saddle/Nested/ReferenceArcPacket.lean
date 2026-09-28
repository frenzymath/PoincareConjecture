import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceLowerSourceCircles
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceLowerEndGeometry
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceComparisonFillings
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.RelativeExteriorArc
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Function Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower

structure ReferenceNormalPacket
    (c : Fin 2 → UnitCircle → E2) (carrier delta : Set E2) (v : E2) where
  W : Fin 2 → Set E2
  Uc : Set UnitCircle
  w : ℝ
  N : OpenPartialHomeomorph (UnitCircle × ℝ) E2
  hWopen : ∀ i, IsOpen (W i)
  hWconn : ∀ i, IsConnected (W i)
  hWunbounded : ∀ i, ¬ Bornology.IsBounded (W i)
  hWcurve : ∀ i, Disjoint (W i) (range (c i))
  hFW : ∀ i, carrier \ delta ⊆ W i
  hUc : IsOpen Uc
  hAc : {p : UnitCircle | (2 / 3 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ} ⊆ Uc
  hUcJ : Uc ⊆ {p : UnitCircle | (1 / 2 : ℝ) < ⟪v, (p : E2)⟫_ℝ}
  hw : 0 < w
  hNsource : Uc ×ˢ Icc (-w) w ⊆ N.source
  hN : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E2) ∞ N N.source
  hNinv : ContMDiffOn 𝓘(ℝ, E2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
    N.symm N.target
  hNzero : ∀ p ∈ Uc, N (p, 0) = c 0 p
  hNpositive : ∀ i, N '' (Uc ×ˢ Ioo (0 : ℝ) w) ⊆ W i

set_option linter.unusedVariables false in
set_option maxHeartbeats 1500000 in

theorem exists_reference_arc_packet
    (hP : PlanarSchoenfliesService)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (mu : ℝ) (hmu : 0 < mu) (hmuSmall : mu ≤ 1 / 128)
    (chi : ℝ → ℝ) (hchi : ContDiff ℝ ∞ chi)
    (hchiBounds : ∀ r : ℝ, 0 ≤ chi r ∧ chi r ≤ 1)
    (hchiSupport : tsupport chi ⊆ Ioo (1 / 2 : ℝ) (3 / 2))
    (hchiOne : ∀ r ∈ Icc (3 / 4 : ℝ) (5 / 4), chi r = 1) :
    let F : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞ :=
      Classical.choose (exists_saddle_angular_reconnection
        J2 hJ2 mu hmu hmuSmall chi hchi hchiBounds hchiSupport hchiOne)
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let port : Fin 4 → E2 := fun a =>
      J2.symm (sx a / Real.sqrt 2, sy a / Real.sqrt 2)
    let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
    let sign : Fin 2 → ℝ := ![1, -1]
    let Z : Fin 2 → Set E2 := fun i =>
      {x | ‖x‖ ≤ 1 ∧ (J2 x).2 = sign i *
        Real.sqrt ((J2 x).1 ^ 2 + mu)}
    let Eta : Fin 2 → Set E2 := fun i => (F 1) '' Z i
    ∀ (nuRef : ℝ) (hnuRef : 0 < nuRef) (hnuRefSmall : nuRef < 1 / 16)
      (alphaRef : Fin 2 → ℝ → E2)
      (hReferenceArcs : ∀ i : Fin 2,
        ContDiffOn ℝ ∞ (alphaRef i) (Ioo (-nuRef) (1 + nuRef)) ∧
        InjOn (alphaRef i) (Ioo (-nuRef) (1 + nuRef)) ∧
        (∀ t ∈ Ioo (-nuRef) (1 + nuRef), deriv (alphaRef i) t ≠ 0) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, 0 < sign i * (J2 (alphaRef i t)).2) ∧
        (∀ t ∈ Ioo (0 : ℝ) 1, 1 < ‖alphaRef i t‖) ∧
        (∀ t : ℝ, |t| < nuRef →
          alphaRef i t = (1 + t) • port (ep (i, 0))) ∧
        (∀ t : ℝ, |t - 1| < nuRef →
          alphaRef i t = (2 - t) • port (ep (i, 1))))
      (hReferencePair : Disjoint (alphaRef 0 '' Icc (0 : ℝ) 1)
        (alphaRef 1 '' Icc (0 : ℝ) 1))
      (carrier : Set E2) (v : E2) (Dc : Set UnitCircle)
      (hNormal : ∀ (c : Fin 2 → UnitCircle → E2),
        (∀ i, IsPlanarEmbedding (c i)) →
        ReferenceNormalPacket c carrier (c 0 '' Dc) v),
      ∃ (cRef : Fin 2 → UnitCircle → E2)
        (BRef : Fin 2 → BallNeighborhoodChart E2 E2),
        ∃ packet : ReferenceNormalPacket cRef carrier (cRef 0 '' Dc) v,
        (∀ i, IsPlanarEmbedding (cRef i)) ∧
        (∀ i, range (cRef i) =
          (alphaRef i '' Icc (0 : ℝ) 1) ∪ Eta i) ∧
        (∀ i, (BRef i).boundary = range (cRef i)) ∧
        (∀ i, (BRef i).closedRegion ⊆
          {x : E2 | 0 < sign i * (J2 x).2}) ∧
        Disjoint (BRef 0).closedRegion (BRef 1).closedRegion ∧
        Disjoint (alphaRef 0 '' Icc (0 : ℝ) 1)
          (alphaRef 1 '' Icc (0 : ℝ) 1) := by
  classical
  dsimp only
  intro nuRef hnuRef hnuRefSmall alphaRef hReferenceArcs hReferencePair
    carrier v Dc hNormal
  let F := Classical.choose (exists_saddle_angular_reconnection
    J2 hJ2 mu hmu hmuSmall chi hchi hchiBounds hchiSupport hchiOne)
  let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
  let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
  let port : Fin 4 → E2 := fun a => J2.symm (sx a / Real.sqrt 2, sy a / Real.sqrt 2)
  let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
  let sign : Fin 2 → ℝ := ![1, -1]
  let Z : Fin 2 → Set E2 := fun i =>
    {x | ‖x‖ ≤ 1 ∧ (J2 x).2 = sign i * Real.sqrt ((J2 x).1 ^ 2 + mu)}
  let Eta : Fin 2 → Set E2 := fun i => (F 1) '' Z i
  obtain ⟨cRef, BRef, hcRef, hcRefImage, hBRef, hBRefHalfPlane,
    hBRefDisjoint⟩ := exists_nonnested_reference_comparison_fillings hP J2 hJ2
      mu hmu hmuSmall chi hchi hchiBounds hchiSupport hchiOne nuRef hnuRef
      hnuRefSmall alphaRef
      (fun i => (hReferenceArcs i).1)
      (fun i => (hReferenceArcs i).2.1)
      (fun i => (hReferenceArcs i).2.2.1)
      (fun i => (hReferenceArcs i).2.2.2.1)
      (fun i => (hReferenceArcs i).2.2.2.2.1)
      (fun i => (hReferenceArcs i).2.2.2.2.2.1)
      (fun i => (hReferenceArcs i).2.2.2.2.2.2)
  refine ⟨cRef, BRef, hNormal cRef hcRef, hcRef, hcRefImage, hBRef,
    hBRefHalfPlane, hBRefDisjoint, hReferencePair⟩

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
