import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.LongSectorTemplates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhoodNesting
import Mathlib.Tactic











set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

set_option linter.unusedVariables false in

set_option maxHeartbeats 1000000 in




theorem saddle_nested_raised_long_return_outer_closed
    (kappa : OpenPartialHomeomorph E2 E2)
    (B : BallNeighborhoodChart E2 E2)
    (alpha gamma : ℝ → E2) (Eta Ray : Set E2)
    (h : ℝ) (l r : ℝ)
    (hh : 0 < h) (hhalf : h < 1 / 2)
    (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ 1)
    (hleftRoom : h ≤ l) (hrightRoom : r + h ≤ 1)
    (hBoundary : B.boundary = alpha '' Icc (0 : ℝ) 1 ∪ Eta)
    (hEtaUnit : Eta ⊆ kappa '' closedBall (0 : E2) 1)
    (hAnnular :
      (alpha '' Icc (0 : ℝ) 1) ∩
          (kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h}) =
        kappa '' Ray)
    (hActiveAnnulus : gamma '' Ioo h (1 - h) ⊆
      kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h})
    (hActiveRayDisjoint :
      Disjoint (gamma '' Ioo h (1 - h)) (kappa '' Ray))
    (hActiveUnitDisjoint :
      Disjoint (gamma '' Ioo h (1 - h))
        (kappa '' closedBall (0 : E2) 1))
    (hActivePreconnected : IsPreconnected (gamma '' Ioo h (1 - h)))
    (hGammaContinuous : ContinuousOn gamma (Icc (0 : ℝ) 1))
    (hMidpoint : gamma (1 / 2) ∈ B.inside)
    (hGermLeft : ∀ t ∈ Icc (0 : ℝ) h, gamma t = alpha (r + t))
    (hGermRight : ∀ t ∈ Icc (1 - h) 1, gamma t = alpha (l + t - 1))
    (hAlphaInj : InjOn alpha (Icc (0 : ℝ) 1)) :
    gamma '' Ioo h (1 - h) ⊆ B.inside ∧
      gamma '' Icc (0 : ℝ) 1 ⊆ B.closedRegion ∧
      (gamma '' Icc (0 : ℝ) 1) ∩ (alpha '' Icc l r) =
        {gamma 0, gamma 1} := by
  have hActiveAlphaDisjoint :
      Disjoint (gamma '' Ioo h (1 - h)) (alpha '' Icc (0 : ℝ) 1) := by
    apply Set.disjoint_left.mpr
    intro y hyGamma hyAlpha
    have hyAnn : y ∈ kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h} :=
      hActiveAnnulus hyGamma
    have hyRay : y ∈ kappa '' Ray := by
      have hyPair : y ∈
          (alpha '' Icc (0 : ℝ) 1) ∩
            (kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h}) :=
        ⟨hyAlpha, hyAnn⟩
      rw [hAnnular] at hyPair
      exact hyPair
    exact (Set.disjoint_left.mp hActiveRayDisjoint hyGamma) hyRay
  have hActiveBoundaryDisjoint :
      Disjoint (gamma '' Ioo h (1 - h)) B.boundary := by
    apply Set.disjoint_left.mpr
    intro y hyGamma hyBoundary
    rw [hBoundary] at hyBoundary
    rcases hyBoundary with hyAlpha | hyEta
    · exact (Set.disjoint_left.mp hActiveAlphaDisjoint hyGamma) hyAlpha
    · exact (Set.disjoint_left.mp hActiveUnitDisjoint hyGamma)
        (hEtaUnit hyEta)
  have hActiveInside : gamma '' Ioo h (1 - h) ⊆ B.inside := by
    rcases B.preconnected_subset_inside_or_outside
        hActivePreconnected hActiveBoundaryDisjoint with hi | ho
    · exact hi
    · exfalso
      apply ho
        (⟨(1 / 2 : ℝ), ⟨by linarith, by linarith⟩, rfl⟩)
      rw [← B.inside_union_boundary]
      exact Or.inl hMidpoint
  have hBoundaryClosed : B.boundary ⊆ B.closedRegion := by
    intro y hy
    rw [← B.inside_union_boundary]
    exact Or.inr hy
  have hActiveClosed : gamma '' Ioo h (1 - h) ⊆ B.closedRegion := by
    intro y hy
    rw [← B.inside_union_boundary]
    exact Or.inl (hActiveInside hy)
  have hClosedRegion : gamma '' Icc (0 : ℝ) 1 ⊆ B.closedRegion := by
    rintro y ⟨t, ht, rfl⟩
    by_cases hmid : t ∈ Ioo h (1 - h)
    · exact hActiveClosed ⟨t, hmid, rfl⟩
    · rcases le_or_gt t h with htLeft | htLeft
      · have htTail : t ∈ Icc (0 : ℝ) h := ⟨ht.1, htLeft⟩
        rw [hGermLeft t htTail]
        apply hBoundaryClosed
        rw [hBoundary]
        have hrt : r + t ∈ Icc (0 : ℝ) 1 :=
          ⟨by linarith [hl, hlr, ht.1], by linarith [hrightRoom, htLeft]⟩
        exact Or.inl ⟨r + t, hrt, rfl⟩
      · have htRight : 1 - h ≤ t := by
          by_contra hn
          exact hmid ⟨htLeft, lt_of_not_ge hn⟩
        have htTail : t ∈ Icc (1 - h) 1 := ⟨htRight, ht.2⟩
        rw [hGermRight t htTail]
        apply hBoundaryClosed
        rw [hBoundary]
        have hlt : l + t - 1 ∈ Icc (0 : ℝ) 1 :=
          ⟨by linarith [hleftRoom, htRight], by linarith [hl, hr, ht.2]⟩
        exact Or.inl ⟨l + t - 1, hlt, rfl⟩
  have hTrimDisjoint :
      Disjoint (gamma '' Ioo h (1 - h)) (alpha '' Icc l r) :=
    hActiveAlphaDisjoint.mono_right (image_mono (Icc_subset_Icc hl hr))
  have hIntersectionForward :
      (gamma '' Icc (0 : ℝ) 1) ∩ (alpha '' Icc l r) ⊆
        {gamma 0, gamma 1} := by
    rintro y ⟨⟨t, ht, rfl⟩, ⟨s, hs, hys⟩⟩
    by_cases hmid : t ∈ Ioo h (1 - h)
    · exact False.elim ((Set.disjoint_left.mp hTrimDisjoint
        ⟨t, hmid, rfl⟩) ⟨s, hs, hys⟩)
    · rcases le_or_gt t h with htLeft | htLeft
      · have htTail : t ∈ Icc (0 : ℝ) h := ⟨ht.1, htLeft⟩
        have heq : alpha (r + t) = alpha s := by
          rw [← hGermLeft t htTail]
          exact hys.symm
        have hrt : r + t ∈ Icc (0 : ℝ) 1 :=
          ⟨by linarith [hl, hlr, ht.1], by linarith [hrightRoom, htLeft]⟩
        have hs01 : s ∈ Icc (0 : ℝ) 1 :=
          ⟨by linarith [hl, hs.1], by linarith [hr, hs.2]⟩
        have hst : r + t = s := hAlphaInj hrt hs01 heq
        have ht0 : t = 0 := by linarith [ht.1, hs.2, hst]
        subst t
        exact Or.inl rfl
      · have htRight : 1 - h ≤ t := by
          by_contra hn
          exact hmid ⟨htLeft, lt_of_not_ge hn⟩
        have htTail : t ∈ Icc (1 - h) 1 := ⟨htRight, ht.2⟩
        have heq : alpha (l + t - 1) = alpha s := by
          rw [← hGermRight t htTail]
          exact hys.symm
        have hlt : l + t - 1 ∈ Icc (0 : ℝ) 1 :=
          ⟨by linarith [hleftRoom, htRight], by linarith [hl, hr, ht.2]⟩
        have hs01 : s ∈ Icc (0 : ℝ) 1 :=
          ⟨by linarith [hl, hs.1], by linarith [hr, hs.2]⟩
        have hst : l + t - 1 = s := hAlphaInj hlt hs01 heq
        have ht1 : t = 1 := by linarith [ht.2, hs.1, hst]
        subst t
        exact Or.inr rfl
  have hIntersectionReverse :
      {gamma 0, gamma 1} ⊆
        (gamma '' Icc (0 : ℝ) 1) ∩ (alpha '' Icc l r) := by
    intro y hy
    rcases hy with rfl | rfl
    · refine ⟨⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩, ?_⟩
      rw [hGermLeft 0 ⟨by norm_num, by linarith⟩]
      exact ⟨r, ⟨hlr, le_rfl⟩, by ring_nf⟩
    · refine ⟨⟨1, ⟨by norm_num, by norm_num⟩, rfl⟩, ?_⟩
      rw [hGermRight 1 ⟨by linarith, by norm_num⟩]
      exact ⟨l, ⟨le_rfl, hlr⟩, by ring_nf⟩
  exact ⟨hActiveInside, hClosedRegion,
    Set.Subset.antisymm hIntersectionForward hIntersectionReverse⟩

end PoincareConjecture.M25.Topology3D
