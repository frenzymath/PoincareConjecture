import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Step
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Reverse.FilledSides



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

namespace Reverse



structure MarkedCapLens
    (B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞) (g : E2 → E3) {v : E3}
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞) (c s : Real) where
  F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞
  childMark : E2 → S2
  lensMark : E2 → S2
  childMark_injective : InjOn childMark (closedBall 0 1)
  lensMark_injective : InjOn lensMark (closedBall 0 1)
  childMark_local : ∀ x ∈ closedBall (0 : E2) 1,
    IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ childMark x
  lensMark_local : ∀ x ∈ closedBall (0 : E2) 1,
    IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ lensMark x
  childMark_eq : ∀ x ∈ closedBall (0 : E2) 1, B (childMark x : E3) = g x
  lensMark_eq : ∀ x ∈ closedBall (0 : E2) 1, F (lensMark x : E3) = g x
  boundary_intersection : (B '' sphere (0 : E3) 1) ∩ (F '' sphere (0 : E3) 1) =
    g '' closedBall (0 : E2) 1
  marked_disk : (fun x => B (childMark x : E3)) '' closedBall (0 : E2) 1 =
    g '' closedBall (0 : E2) 1
  marked_edge : (fun x => B (childMark x : E3)) '' sphere (0 : E2) 1 =
    g '' sphere (0 : E2) 1
  strict_projection : ∀ y ∈ (F '' sphere (0 : E3) 1) \ (g '' closedBall (0 : E2) 1),
    (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' ball 0 1
  filled_bounds : ∀ y ∈ F '' closedBall (0 : E3) 1,
    (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ A '' closedBall 0 1 ∧
    |inner Real v y - c| ≤ 2 * |s|
  filled_placement : F '' closedBall (0 : E3) 1 ⊆ B '' closedBall (0 : E3) 1 ∨
    (B '' closedBall (0 : E3) 1) ∩ (F '' closedBall (0 : E3) 1) =
      g '' closedBall (0 : E2) 1

private theorem exists_markedCapLens
    {v : E3} (hv : ‖v‖ = 1) (c s : Real) (hs : s ≠ 0)
    (A : Diffeomorph 𝓘(Real, Hemisphere.Plane v) 𝓘(Real, Hemisphere.Plane v)
      (Hemisphere.Plane v) (Hemisphere.Plane v) ∞)
    (g : E2 → E3) (hg : ContDiff Real ∞ g) (hgi : Injective g)
    (hgder : ∀ x, Injective (fderiv Real g x))
    (hcore : g '' closedBall (0 : E2) 1 =
      Poincare.Geometry.Euclidean.liftPlaneDiffeomorph hv c s hs A ''
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
    Nonempty (MarkedCapLens B g A c s) := by
  obtain ⟨F, m, n, hmi, hni, hml, hnl, hmark, hmeet, hclosed, hedge,
    hstrict, hbound⟩ := exists_common_marked_unit_cap_lens hv c s hs A g hg hgi hgder
      hcore hf B hboundary d hd hdi hsource hpatch retained hrange hclear
  have havoid : Disjoint (F '' ball (0 : E3) 1) (B '' sphere (0 : E3) 1) := by
    apply disjoint_left.mpr
    intro y hyF hyB
    have hyFc := (image_mono ball_subset_closedBall) hyF
    have hproj := projection_mem_open_disk_of_mem_open_body A F.toHomeomorph
      (fun z hz => (hbound z hz).1) hyF
    rw [hboundary, hrange] at hyB
    rcases hyB with hycap | hyretained
    · obtain ⟨x, hx, rfl⟩ := hycap
      obtain ⟨z, hz, hzx⟩ := hyF
      have hzn : z = (n x : E3) := F.injective (hzx.trans (hmark x hx).2.symm)
      rw [hzn] at hz
      exact (ne_of_lt (mem_ball_zero_iff.mp hz)) (norm_eq_of_mem_sphere (n x))
    · have hboundaryProj := hclear y hyretained (hbound y hyFc).1 (hbound y hyFc).2
      obtain ⟨x, hx, hxy⟩ := hproj
      obtain ⟨z, hz, hzy⟩ := hboundaryProj
      have hxz : x = z := A.injective (hxy.trans hzy.symm)
      rw [hxz] at hx
      exact (ne_of_lt (mem_ball_zero_iff.mp hx)) (mem_sphere_zero_iff_norm.mp hz)
  have hplacement := filled_ball_subset_or_inter_eq_boundary
    B.toHomeomorph F.toHomeomorph havoid
  have hmeet' : (B '' sphere (0 : E3) 1) ∩ (F '' sphere (0 : E3) 1) =
      g '' closedBall (0 : E2) 1 := hmeet.trans hclosed
  refine ⟨{
    F := F
    childMark := m
    lensMark := n
    childMark_injective := hmi
    lensMark_injective := hni
    childMark_local := hml
    lensMark_local := hnl
    childMark_eq := fun x hx => (hmark x hx).1
    lensMark_eq := fun x hx => (hmark x hx).2
    boundary_intersection := hmeet'
    marked_disk := hclosed
    marked_edge := hedge
    strict_projection := hstrict
    filled_bounds := hbound
    filled_placement := ?_ }⟩
  rcases hplacement with hin | hout
  · exact Or.inl hin
  · exact Or.inr (hout.trans hmeet')

end Reverse

namespace SphereSurgeryStep

variable {f : S2 → E3} {v : E3} {c R : Real} (S : SphereSurgeryStep f v c R)


theorem projection_mem_circle_of_mem_prepared
    {y : E3} (hy : y ∈ range (fun p => S.D (f p)))
    (hproj : (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' closedBall 0 1)
    (hheight : |inner Real v y - c| ≤ 2 * S.a) :
    (Hemisphere.Plane v).orthogonalProjectionOnto y ∈ S.A '' sphere 0 1 := by
  let t := inner Real v y - c
  have ht : t ∈ Icc (-(2 * S.a)) (2 * S.a) := abs_le.mp hheight
  obtain ⟨z, hz, hzy⟩ := hproj
  have hyplane : y ∈
      (fun x : Hemisphere.Plane v => (c + t) • v + (S.A x : E3)) '' closedBall 0 1 := by
    refine ⟨z, hz, ?_⟩
    have heq := (Poincare.Geometry.Euclidean.heightCoordinates S.unit_v).apply_symm_apply y
    change inner Real v y • v +
      ((Hemisphere.Plane v).orthogonalProjectionOnto y : E3) = y at heq
    rw [← hzy] at heq
    rw [show c + t = inner Real v y by dsimp [t]; ring]
    exact heq
  obtain ⟨p, ⟨q, rfl⟩, hqy⟩ := (S.parallel_disk_intersection t ht) ▸
    (show y ∈ ((fun x : Hemisphere.Plane v => (c + t) • v + (S.A x : E3)) ''
      closedBall 0 1) ∩ range (fun p => S.D (f p)) from ⟨hyplane, hy⟩)
  change S.D (f (S.T (q, t))) = y at hqy
  rw [← hqy, S.cylinder q t ⟨by linarith [ht.1, S.a_lt_quarter_ε, S.a_pos],
    by linarith [ht.2, S.a_lt_quarter_ε, S.a_pos]⟩, S.circle_image]
  simp [Hemisphere.Plane,
    Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero]



theorem exists_capMinus_lens
    (B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hB : B '' sphere (0 : E3) 1 = range S.fMinus) :
    Nonempty (Reverse.MarkedCapLens B S.gMinus S.A (c - S.a) S.s) := by
  apply Reverse.exists_markedCapLens S.unit_v (c - S.a) S.s S.s_pos.ne' S.A
    S.gMinus S.gMinus_smooth S.gMinus_injective S.gMinus_deriv_injective S.gMinus_range
    S.fMinus_embedding B hB S.dMinus S.dMinus_smooth S.dMinus_symm_smooth
    S.dMinus_source S.capMinus_eq
    ((fun p => S.D (f p)) '' (S.eMinus '' closedBall 0 1)) S.fMinus_range
  rintro y ⟨p, _, rfl⟩ hproj hheight
  apply S.projection_mem_circle_of_mem_prepared (mem_range_self p) hproj
  rw [abs_of_pos S.s_pos] at hheight
  obtain ⟨hl, hu⟩ := abs_le.mp hheight
  exact abs_le.mpr ⟨by linarith [S.s_lt_eighth_a, S.a_pos],
    by linarith [S.s_lt_eighth_a, S.a_pos]⟩



theorem exists_capPlus_lens
    (B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hB : B '' sphere (0 : E3) 1 = range S.fPlus) :
    Nonempty (Reverse.MarkedCapLens B S.gPlus S.A (c + S.a) (-S.s)) := by
  apply Reverse.exists_markedCapLens S.unit_v (c + S.a) (-S.s)
    (neg_ne_zero.mpr S.s_pos.ne') S.A S.gPlus S.gPlus_smooth S.gPlus_injective
    S.gPlus_deriv_injective S.gPlus_range S.fPlus_embedding B hB
    S.dPlus S.dPlus_smooth S.dPlus_symm_smooth S.dPlus_source S.capPlus_eq
    ((fun p => S.D (f p)) '' (S.ePlus '' closedBall 0 1)) S.fPlus_range
  rintro y ⟨p, _, rfl⟩ hproj hheight
  apply S.projection_mem_circle_of_mem_prepared (mem_range_self p) hproj
  rw [abs_neg, abs_of_pos S.s_pos] at hheight
  obtain ⟨hl, hu⟩ := abs_le.mp hheight
  exact abs_le.mpr ⟨by linarith [S.s_lt_eighth_a, S.a_pos],
    by linarith [S.s_lt_eighth_a, S.a_pos]⟩

end SphereSurgeryStep

end Poincare.Manifold.Schoenflies
