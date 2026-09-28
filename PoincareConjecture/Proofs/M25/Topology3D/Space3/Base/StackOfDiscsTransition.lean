import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerEndTubePrimitives
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallRegionUniqueness

set_option autoImplicit false

open Set Metric
open scoped ContDiff

namespace PoincareConjecture.M25.Topology3D

theorem stackDiscTransition_spec
    (T G : OpenPartialHomeomorph (E2 × ℝ) (E2 × ℝ))
    (hT : ContDiffOn ℝ ∞ T T.source) (hTi : ContDiffOn ℝ ∞ T.symm T.target)
    (hG : ContDiffOn ℝ ∞ G G.source) (hGi : ContDiffOn ℝ ∞ G.symm G.target)
    (hTh : ∀ p ∈ T.source, (T p).2 = p.2)
    (hGh : ∀ p ∈ G.source, (G p).2 = p.2)
    (I : Set ℝ)
    (hTs : closedBall (0 : E2) 1 ×ˢ I ⊆ T.source)
    (hGs : closedBall (0 : E2) 1 ×ˢ I ⊆ G.source)
    (hboundary : ∀ z ∈ I,
      (fun x : E2 => (T (x, z)).1) '' sphere (0 : E2) 1 =
        (fun x : E2 => (G (x, z)).1) '' sphere (0 : E2) 1) :
    let E := T.trans G.symm
    ContDiffOn ℝ ∞ E E.source ∧ ContDiffOn ℝ ∞ E.symm E.target ∧
      (∀ p ∈ E.source, (E p).2 = p.2) ∧
      (∀ p ∈ E.target, (E.symm p).2 = p.2) ∧
      (closedBall (0 : E2) 1 ×ˢ I ⊆ E.source) ∧
      (closedBall (0 : E2) 1 ×ˢ I ⊆ E.target) ∧
      ∀ J : Set ℝ, J ⊆ I → ∀ A : Set E2,
        (A = ball 0 1 ∨ A = closedBall 0 1 ∨ A = sphere 0 1) →
        E '' (A ×ˢ J) = A ×ˢ J ∧ E.symm '' (A ×ˢ J) = A ×ˢ J := by
  let E := T.trans G.symm
  have hTih (p : E2 × ℝ) (hp : p ∈ T.target) : (T.symm p).2 = p.2 := by
    have hh := hTh (T.symm p) (T.map_target hp)
    rw [T.right_inv hp] at hh
    exact hh.symm
  have hGih (p : E2 × ℝ) (hp : p ∈ G.target) : (G.symm p).2 = p.2 := by
    have hh := hGh (G.symm p) (G.map_target hp)
    rw [G.right_inv hp] at hh
    exact hh.symm
  have hEh (p : E2 × ℝ) (hp : p ∈ E.source) : (E p).2 = p.2 :=
    (hGih (T p) hp.2).trans (hTh p hp.1)
  have hEih (p : E2 × ℝ) (hp : p ∈ E.target) : (E.symm p).2 = p.2 :=
    (hTih (G p) hp.2).trans (hGh p hp.1)
  have hregion (z : ℝ) (hz : z ∈ I) (A : Set E2)
      (hA : A = ball 0 1 ∨ A = closedBall 0 1 ∨ A = sphere 0 1) :
      (fun x : E2 => (T (x, z)).1) '' A =
        (fun x : E2 => (G (x, z)).1) '' A := by
    obtain ⟨N, hN, _, _, _⟩ := exists_saddle_end_fiber_chart T hT hTi hTh z
      (fun x hx => hTs ⟨hx, hz⟩)
    obtain ⟨D, hD, _, _, _⟩ := exists_saddle_end_fiber_chart G hG hGi hGh z
      (fun x hx => hGs ⟨hx, hz⟩)
    have hNimage (S : Set E2) : N.chart '' S = (fun x => (T (x, z)).1) '' S :=
      image_congr (fun x _ => hN x)
    have hDimage (S : Set E2) : D.chart '' S = (fun x => (G (x, z)).1) '' S :=
      image_congr (fun x _ => hD x)
    have hbound : N.boundary = D.boundary :=
      (hNimage _).trans ((hboundary z hz).trans (hDimage _).symm)
    have hdim : 1 < Module.rank ℝ E2 :=
      Module.one_lt_rank_of_one_lt_finrank (by simp [E2])
    rcases hA with rfl | rfl | rfl
    · exact (hNimage _).symm.trans
        ((N.inside_eq_of_boundary_eq D hdim hbound).trans (hDimage _))
    · exact (hNimage _).symm.trans
        ((N.closedRegion_eq_of_boundary_eq D hdim hbound).trans (hDimage _))
    · exact hboundary z hz
  have hAsub (A : Set E2)
      (hA : A = ball 0 1 ∨ A = closedBall 0 1 ∨ A = sphere 0 1) :
      A ⊆ closedBall (0 : E2) 1 := by
    rcases hA with rfl | rfl | rfl
    · exact ball_subset_closedBall
    · exact subset_rfl
    · exact sphere_subset_closedBall
  have hmove (z : ℝ) (hz : z ∈ I) (A : Set E2)
      (hA : A = ball 0 1 ∨ A = closedBall 0 1 ∨ A = sphere 0 1) :
      (∀ x ∈ A, (x, z) ∈ E.source ∧ (E (x, z)).1 ∈ A) ∧
      (∀ y ∈ A, (y, z) ∈ E.target ∧ (E.symm (y, z)).1 ∈ A) := by
    have hreg := hregion z hz A hA
    have hsub := hAsub A hA
    constructor
    · intro x hx
      have hxs : (x, z) ∈ T.source := hTs ⟨hsub hx, hz⟩
      have hm : (T (x, z)).1 ∈ (fun y : E2 => (G (y, z)).1) '' A := by
        rw [← hreg]
        exact ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyeq⟩ := hm
      have hys : (y, z) ∈ G.source := hGs ⟨hsub hy, hz⟩
      have heq : G (y, z) = T (x, z) :=
        Prod.ext hyeq ((hGh _ hys).trans (hTh _ hxs).symm)
      have hsrc : (x, z) ∈ E.source := by
        refine ⟨hxs, ?_⟩
        change T (x, z) ∈ G.target
        rw [← heq]
        exact G.map_source hys
      refine ⟨hsrc, ?_⟩
      change (G.symm (T (x, z))).1 ∈ A
      rw [← heq, G.left_inv hys]
      exact hy
    · intro y hy
      have hys : (y, z) ∈ G.source := hGs ⟨hsub hy, hz⟩
      have hm : (G (y, z)).1 ∈ (fun x : E2 => (T (x, z)).1) '' A := by
        rw [hreg]
        exact ⟨y, hy, rfl⟩
      obtain ⟨x, hx, hxeq⟩ := hm
      have hxs : (x, z) ∈ T.source := hTs ⟨hsub hx, hz⟩
      have heq : T (x, z) = G (y, z) :=
        Prod.ext hxeq ((hTh _ hxs).trans (hGh _ hys).symm)
      have htar : (y, z) ∈ E.target := by
        refine ⟨hys, ?_⟩
        change G (y, z) ∈ T.target
        rw [← heq]
        exact T.map_source hxs
      refine ⟨htar, ?_⟩
      change (T.symm (G (y, z))).1 ∈ A
      rw [← heq, T.left_inv hxs]
      exact hx
  refine ⟨hGi.comp (hT.mono inter_subset_left) (fun _ hp => hp.2),
    hTi.comp (hG.mono inter_subset_left) (fun _ hp => hp.2), hEh, hEih, ?_, ?_, ?_⟩
  · intro p hp
    exact ((hmove p.2 hp.2 _ (Or.inr (Or.inl rfl))).1 p.1 hp.1).1
  · intro p hp
    exact ((hmove p.2 hp.2 _ (Or.inr (Or.inl rfl))).2 p.1 hp.1).1
  · intro J hJI A hA
    have hf (p : E2 × ℝ) (hp : p ∈ A ×ˢ J) :
        p ∈ E.source ∧ E p ∈ A ×ˢ J := by
      obtain ⟨hs, hm⟩ := (hmove p.2 (hJI hp.2) A hA).1 p.1 hp.1
      exact ⟨hs, hm, (hEh p hs).symm ▸ hp.2⟩
    have hi (p : E2 × ℝ) (hp : p ∈ A ×ˢ J) :
        p ∈ E.target ∧ E.symm p ∈ A ×ˢ J := by
      obtain ⟨ht, hm⟩ := (hmove p.2 (hJI hp.2) A hA).2 p.1 hp.1
      exact ⟨ht, hm, (hEih p ht).symm ▸ hp.2⟩
    constructor
    · apply Subset.antisymm
      · rintro _ ⟨p, hp, rfl⟩
        exact (hf p hp).2
      · intro p hp
        exact ⟨E.symm p, (hi p hp).2, E.right_inv (hi p hp).1⟩
    · apply Subset.antisymm
      · rintro _ ⟨p, hp, rfl⟩
        exact (hi p hp).2
      · intro p hp
        exact ⟨E p, (hf p hp).2, E.left_inv (hf p hp).1⟩

end PoincareConjecture.M25.Topology3D
