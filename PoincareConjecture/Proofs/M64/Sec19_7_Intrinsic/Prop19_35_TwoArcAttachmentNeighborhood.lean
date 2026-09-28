import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcCapSeparators
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ChosenCapGeometry

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture

theorem m64Intrinsic_exists_arc_cap_attachment_neighborhood
    {gamma : ℝ → AnnulusCoordinates} {T r : ℝ} (hr : 0 < r) (hrT : r < T)
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (F : Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (hsource : ∀ i,
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ (F i).source)
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (F i).source)
    (hFi : ∀ i, ContDiffOn ℝ ∞ (F i).symm (F i).target)
    (hfirst : ∀ i, ∀ s ∈ Icc (0 : ℝ) r,
      F i (s, 0) = H (sectorParameterEquiv 0 i (s, 0)))
    (hsecond : ∀ i, ∀ s ∈ Icc (0 : ℝ) r,
      F i (0, s) = H (sectorParameterEquiv 0 i (0, s)))
    (hsector : ∀ i,
      F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆
        H '' (H.source ∩ (sectorParameterEquiv 0 i) ''
          {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (positive terminal vertical : Bool)
    (haxis : ∀ s : ℝ, H (if vertical then (0, s) else (s, 0)) =
      gamma (if terminal then T - s else s))
    (htipSource : (if vertical then ((0 : ℝ), r) else (r, 0)) ∈ H.source) :
    let selected := if vertical then (positive, true) else (true, positive)
    let occupied (i : Bool × Bool) := if positive then i = (true, true) else i ≠ (true, true)
    let caps (i : Bool × Bool) :=
      F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
    let C := ⋃ i, ⋃ (_ : occupied i), caps i
    ∃ N : Set AnnulusCoordinates,
      IsOpen N ∧ gamma (if terminal then T - r else r) ∈ N ∧
      N ∩ C ⊆ caps selected ∧
      N ∩ frontier (caps selected) ⊆ gamma '' Icc 0 T ∪
        (fun t : ℝ => F selected ((1 - t) * r, t * r)) '' Icc (0 : ℝ) 1 ∧
      F selected (if vertical then (r, 0) else (0, r)) ∉ N := by
  classical
  dsimp only
  let selected := if vertical then (positive, true) else (true, positive)
  let occupied (i : Bool × Bool) := if positive then i = (true, true) else i ≠ (true, true)
  let caps (i : Bool × Bool) :=
    F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
  obtain ⟨face, hc, hz, ho, ht, _⟩ :=
    m64Intrinsic_exists_coordinate_face_of_chosen_cap (F selected) hr
      (hsource selected) (hF selected) (hFi selected)
  let other : Fin 3 := if vertical then 2 else 1
  let foreign := ⋃ i : Bool × Bool, ⋃ (_ : occupied i ∧ i ≠ selected), caps i
  let K := foreign ∪ (face.boundary other).map '' Icc (0 : ℝ) 1
  have hforeign : IsCompact foreign := isCompact_iUnion (fun i =>
    isCompact_iUnion (fun _ => m64Intrinsic_cap_isCompact (F i) (hsource i)))
  have hK : IsCompact K := hforeign.union
    (isCompact_Icc.image_of_continuousOn (face.boundary other).smooth.continuousOn)
  have hselectedAxis (s : ℝ) (hs : s ∈ Icc (0 : ℝ) r) :
      F selected (if vertical then (0, s) else (s, 0)) =
        gamma (if terminal then T - s else s) := by
    cases vertical
    · calc
        F selected (s, 0) = H (s, 0) := by
          simpa [selected, sectorParameterEquiv_apply] using hfirst (true, positive) s hs
        _ = gamma (if terminal then T - s else s) := haxis s
    · calc
        F selected (0, s) = H (0, s) := by
          simpa [selected, sectorParameterEquiv_apply] using hsecond (positive, true) s hs
        _ = gamma (if terminal then T - s else s) := haxis s
  have htip := hselectedAxis r ⟨hr.le, le_rfl⟩
  have hpK : gamma (if terminal then T - r else r) ∉ K := by
    rintro (hpforeign | hpother)
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hpforeign
      obtain ⟨⟨hio, hineq⟩, hi⟩ := mem_iUnion.mp hi
      apply hineq
      apply m64Intrinsic_corner_cap_tip_unique H hr positive vertical htipSource F hsector i hio
      rwa [haxis]
    · obtain ⟨t, htr, htp⟩ := hpother
      have htr' : t * r ∈ Icc (0 : ℝ) r :=
        ⟨mul_nonneg htr.1 hr.le, by nlinarith [htr.2]⟩
      rw [← htip] at htp
      cases vertical
      · change (face.boundary 1).map t = F selected (r, 0) at htp
        rw [ho] at htp
        have hs0 : (0, t * r) ∈ (F selected).source :=
          hsource selected ⟨le_rfl, htr'.1, by simpa using htr'.2⟩
        have hs1 : (r, 0) ∈ (F selected).source :=
          hsource selected ⟨hr.le, le_rfl, by simp⟩
        have h := congrArg Prod.fst ((F selected).injOn hs0 hs1 htp)
        exact hr.ne h
      · change (face.boundary 2).map t = F selected (0, r) at htp
        rw [ht] at htp
        have hs0 : (t * r, 0) ∈ (F selected).source :=
          hsource selected ⟨htr'.1, le_rfl, by simpa using htr'.2⟩
        have hs1 : (0, r) ∈ (F selected).source :=
          hsource selected ⟨le_rfl, hr.le, by simp⟩
        have h := congrArg Prod.snd ((F selected).injOn hs0 hs1 htp)
        exact hr.ne h
  refine ⟨Kᶜ, hK.isClosed.isOpen_compl, hpK, ?_, ?_, ?_⟩
  · rintro z ⟨hzK, hzC⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hzC
    obtain ⟨hio, hi⟩ := mem_iUnion.mp hi
    by_cases his : i = selected
    · subst i
      exact hi
    · exact False.elim (hzK (Or.inl (mem_iUnion.mpr
        ⟨i, mem_iUnion.mpr ⟨⟨hio, his⟩, hi⟩⟩)))
  · rintro z ⟨hzK, hzfront⟩
    rw [← hc, face.boundary_carrier] at hzfront
    obtain ⟨k, t, htr, rfl⟩ := mem_iUnion.mp hzfront
    by_cases hko : k = other
    · exact False.elim (hzK (Or.inr ⟨t, htr, by rw [hko]⟩))
    by_cases hk0 : k = 0
    · exact Or.inr ⟨t, htr, by rw [hk0, hz]⟩
    left
    have htr' : t * r ∈ Icc (0 : ℝ) r :=
      ⟨mul_nonneg htr.1 hr.le, by nlinarith [htr.2]⟩
    have heq : (face.boundary k).map t = gamma (if terminal then T - t * r else t * r) := by
      cases vertical
      · have hk : k = 2 := by fin_cases k <;> simp_all [other]
        rw [hk, ht]
        exact hselectedAxis _ htr'
      · have hk : k = 1 := by fin_cases k <;> simp_all [other]
        rw [hk, ho]
        exact hselectedAxis _ htr'
    rw [heq]
    refine ⟨if terminal then T - t * r else t * r, ?_, rfl⟩
    cases terminal
    · exact ⟨htr'.1, htr'.2.trans hrT.le⟩
    · change T - t * r ∈ Icc (0 : ℝ) T
      exact ⟨by linarith [htr'.2], by linarith [htr'.1]⟩
  · intro hzK
    apply hzK
    right
    refine ⟨1, by norm_num, ?_⟩
    cases vertical
    · change (face.boundary 1).map 1 = F selected (0, r)
      simpa only [one_mul] using ho 1
    · change (face.boundary 2).map 1 = F selected (r, 0)
      simpa only [one_mul] using ht 1

end PoincareConjecture
