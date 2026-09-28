import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Projective.CompactLift
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Projective.CompactSide
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Projective.SphereBall
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Projective.PuncturedBallComplement
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.BallExtension.Center
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Projective.BoundaryLift
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.CompactExtension

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.ProjectiveGluing

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S3" => UnitThreeSphere

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M] [T2Space M]
  {p : RealProjectiveThree} {U : Set M}
  (S : StandardPuncturedProjectiveCover M p U)

theorem exists_projected_ball_neighborhood
    (b : OpenPartialHomeomorph E3 S3) (hbs : closedBall 0 1 ⊆ b.source)
    (hb : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source)
    (hbi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target)
    (hBB : Disjoint (b '' closedBall 0 1) (Neg.neg '' (b '' closedBall 0 1)))
    (hpuncture : ∀ q ∈ b '' closedBall 0 1, Quotient.mk' q ≠ p) :
    ∃ e : OpenPartialHomeomorph E3 M,
      closedBall 0 1 ⊆ e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧
      e '' closedBall 0 1 = S.cover '' (b '' closedBall 0 1) := by
  let f : E3 → M := S.cover ∘ b
  have hinj : InjOn f (closedBall 0 1) := by
    intro x hx y hy hxy
    rcases (S.fibers (b x) (b y)
      (hpuncture _ (mem_image_of_mem b hx))
      (hpuncture _ (mem_image_of_mem b hy))).mp hxy with h | h
    · exact b.injOn (hbs hx) (hbs hy) h
    · exact (disjoint_left.mp hBB (mem_image_of_mem b hx)
        ⟨b y, mem_image_of_mem b hy, h.symm⟩).elim
  let d : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 S3 ∞ := {
    toPartialEquiv := b.toPartialEquiv
    open_source := b.open_source
    open_target := b.open_target
    contMDiffOn_toFun := hb
    contMDiffOn_invFun := hbi }
  have hlocal (x : E3) (hx : x ∈ closedBall 0 1) :
      IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ f x :=
    (d.isLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ (hbs hx)).comp (𝓡 3) M
      (S.local_diffeomorph ⟨b x, hpuncture _ (mem_image_of_mem b hx)⟩)
  obtain ⟨e, hes, _, heq, he, hei⟩ :=
    Poincare.exists_openPartialHomeomorph_of_injOn_compact (isCompact_closedBall 0 1) hinj hlocal
  refine ⟨e, hes, he, hei, ?_⟩
  calc
    e '' closedBall 0 1 = f '' closedBall 0 1 := image_congr (fun x hx => heq (hes hx))
    _ = S.cover '' (b '' closedBall 0 1) := image_comp _ _ _

include S in

theorem compact_sphere_region_model
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ U)
    (hregular : closure (interior K) = K)
    (f : UnitTwoSphere → M) (hf : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (hfront : range f = frontier K) :
    (∃ e : OpenPartialHomeomorph E3 M,
      closedBall 0 1 ⊆ e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target ∧ e '' closedBall 0 1 = K) ∨
      Nonempty (StandardPuncturedProjectiveCover M p (interior K)) := by
  let L := {q : S3 | Quotient.mk' q ≠ p ∧ S.cover q ∈ K}
  obtain ⟨hL, hLK, _, hLf, hLreg, hLneg⟩ := S.compact_lift_topology hK hKU hregular
  obtain ⟨F, hF, _, _, _, hFdis, hFlift⟩ := S.exists_smooth_embedded_sphere_lift f hf
    (fun q => hKU (hK.isClosed.frontier_subset (hfront.subset (mem_range_self q))))
  have hnegF : Neg.neg '' range F = range (fun q => -F q) :=
    (range_comp' Neg.neg F).symm
  obtain ⟨b, hbs, hb, hbi, hbF, hBB⟩ := Poincare.Projective.exists_antipodal_disjoint_sphere_ball
    F hF (by rwa [hnegF])
  have hboundary : frontier L = b '' sphere 0 1 ∪ Neg.neg '' (b '' sphere 0 1) := by
    rw [hLf, ← hfront, hFlift, hbF, hnegF]
  rcases eq_antipodal_ball_side_of_frontier hL.isClosed hLreg hLneg
      b hbs hb hbi hBB hboundary with hball | hcomplement
  · left
    have hpuncture (q : S3) (hq : q ∈ b '' closedBall 0 1) : Quotient.mk' q ≠ p :=
      (hball.superset (Or.inl hq)).1
    have himage : S.cover '' (b '' closedBall 0 1) = K := by
      apply Subset.antisymm
      · rintro _ ⟨q, hq, rfl⟩
        exact (hball.superset (Or.inl hq)).2
      · intro x hx
        obtain ⟨q, hq, hqx⟩ := hLK.superset hx
        rcases hball.subset hq with hqB | ⟨z, hzB, rfl⟩
        · exact ⟨q, hqB, hqx⟩
        · have hnz := (PuncturedProjectiveSphere.antipode ⟨z, hpuncture z hzB⟩).property
          have hzq := (S.fibers (-z) z hnz (hpuncture z hzB)).mpr (Or.inr rfl)
          exact ⟨z, hzB, hzq.symm.trans hqx⟩
    obtain ⟨e, hes, he, hei, heimage⟩ :=
      exists_projected_ball_neighborhood S b hbs hb hbi hBB hpuncture
    exact ⟨e, hes, he, hei, heimage.trans himage⟩
  · right
    obtain ⟨a, ha⟩ := Quotient.mk_surjective p
    have haL : a ∉ L := fun h => h.1 ha
    have haP : a ∈ b '' ball 0 1 ∪ Neg.neg '' (b '' ball 0 1) := by
      apply not_not.mp
      exact fun hn => haL (hcomplement.superset hn)
    have hchoose : ∃ a' : S3, Quotient.mk' a' = p ∧ a' ∈ b '' ball 0 1 := by
      rcases haP with haB | ⟨a', ha'B, hna'⟩
      · exact ⟨a, ha, haB⟩
      · refine ⟨a', ?_, ha'B⟩
        have hq : (Quotient.mk' (-a') : RealProjectiveThree) = Quotient.mk' a' :=
          Quotient.sound (Or.inr rfl)
        exact hq.symm.trans ((congrArg Quotient.mk' hna').trans ha)
    obtain ⟨a', ha', ha'B⟩ := hchoose
    obtain ⟨_, c, _, hcs, _, hc, hci, hcB, hc0, _⟩ :=
      Poincare.exists_centered_ball_neighborhood b hbs hb hbi ha'B
    have hcball : c '' ball 0 1 = b '' ball 0 1 := by
      rw [c.image_ball_eq_interior hcs hcB, ← b.image_ball_eq_interior hbs rfl]
    have hcdis : Disjoint (c '' closedBall 0 1) (Neg.neg '' (c '' closedBall 0 1)) := by
      rw [hcB]
      exact hBB
    have hcomp : antipodalBallComplement c = L := by
      rw [antipodalBallComplement, hcball]
      exact hcomplement.symm
    obtain ⟨_, _, T, _⟩ :=
      exists_punctured_cover_ball_complement S a' ha' c hcs hc hci hc0 hcdis
    have htarget : interior (S.cover '' antipodalBallComplement c) = interior K := by
      rw [hcomp, hLK]
    exact ⟨{ T with image_eq := T.image_eq.trans htarget }⟩

end PoincareConjecture.ProjectiveGluing
