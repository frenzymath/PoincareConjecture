import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TwoArcCornerCaps
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapUnionSeparators

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture

theorem m64Intrinsic_corner_cap_tip_unique
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    {r : ℝ} (hr : 0 < r) (positive vertical : Bool)
    (hsource : (if vertical then ((0 : ℝ), r) else (r, 0)) ∈ H.source)
    (F : Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (hsector : ∀ i,
      F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆
        H '' (H.source ∩ (sectorParameterEquiv 0 i) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (i : Bool × Bool) (hi : if positive then i = (true, true) else i ≠ (true, true))
    (hmem : H (if vertical then (0, r) else (r, 0)) ∈
      F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}) :
    i = if vertical then (positive, true) else (true, positive) := by
  obtain ⟨_, ⟨hq, p, hp, rfl⟩, heq⟩ := hsector i hmem
  change 0 ≤ p.1 ∧ 0 ≤ p.2 at hp
  obtain ⟨hp1, hp2⟩ := hp
  have hcoords := H.injOn hq hsource heq
  rcases i with ⟨i, j⟩
  cases positive <;> cases vertical <;> cases i <;> cases j <;>
    simp_all [sectorParameterEquiv_apply]
  all_goals linarith

theorem m64Intrinsic_exists_two_arc_cap_union_separator
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma)
    {T r : ℝ} (hr : 0 < r)
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (F : Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
    (hsource : ∀ i,
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ (F i).source)
    (hF : ∀ i, ContDiffOn ℝ ∞ (F i) (F i).source)
    (hFi : ∀ i, ContDiffOn ℝ ∞ (F i).symm (F i).target)
    (hfirst : ∀ i, ∀ s ∈ Icc (0 : ℝ) r, F i (s, 0) = H (sectorParameterEquiv 0 i (s, 0)))
    (hsecond : ∀ i, ∀ s ∈ Icc (0 : ℝ) r, F i (0, s) = H (sectorParameterEquiv 0 i (0, s)))
    (hchord : ∀ i, ∀ t : ℝ, F i ((1 - t) * r, t * r) =
      (1 - t) • F i (r, 0) + t • F i (0, r))
    (hsector : ∀ i,
      F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆
        H '' (H.source ∩ (sectorParameterEquiv 0 i) '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (positive terminal vertical : Bool)
    (haxis : ∀ s : ℝ, H (if vertical then (0, s) else (s, 0)) =
      gamma (if terminal then T - s else s))
    (htip : (if vertical then ((0 : ℝ), r) else (r, 0)) ∈ H.source) :
    let selected := if vertical then (positive, true) else (true, positive)
    let occupied (i : Bool × Bool) := if positive then i = (true, true) else i ≠ (true, true)
    let D := ⋃ i, ⋃ (_ : occupied i),
      F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
    ∃ (ell : AnnulusCoordinates →L[ℝ] ℝ) (W : Set AnnulusCoordinates),
      IsOpen W ∧ gamma (if terminal then T - r else r) ∈ W ∧
      ell (deriv gamma (if terminal then T - r else r)) = (if terminal then -1 else 1) ∧
      ell (if vertical then F selected (r, 0) - F selected (0, r)
        else F selected (0, r) - F selected (r, 0)) = 0 ∧
      ∀ z ∈ W ∩ D, ell (z - gamma (if terminal then T - r else r)) ≤ 0 := by
  classical
  let selected := if vertical then (positive, true) else (true, positive)
  let occupied (i : Bool × Bool) := if positive then i = (true, true) else i ≠ (true, true)
  let C (i : Bool × Bool) :=
    F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
  have hclosed (i : Bool × Bool) : IsClosed (C i) :=
    (m64Intrinsic_cap_isCompact (F i) (hsource i)).isClosed
  have hselected : ∀ s ∈ Icc (0 : ℝ) r,
      F selected (if vertical then (0, s) else (s, 0)) =
        gamma (if terminal then T - s else s) := by
    intro s hs
    cases vertical
    · calc
        F selected (s, 0) = H (s, 0) := by
          simpa [selected, sectorParameterEquiv_apply] using hfirst (true, positive) s hs
        _ = gamma (if terminal then T - s else s) := haxis s
    · calc
        F selected (0, s) = H (0, s) := by
          simpa [selected, sectorParameterEquiv_apply] using hsecond (positive, true) s hs
        _ = gamma (if terminal then T - s else s) := haxis s
  obtain ⟨ell, W0, hW0, hpW0, hnorm, hker, hsep⟩ :=
    m64Intrinsic_exists_cap_endpoint_separator hg hr (F selected) (hsource selected)
      (hF selected) (hFi selected) (hchord selected) terminal vertical hselected
  let O : Set AnnulusCoordinates := ⋂ i : Bool × Bool,
    if occupied i ∧ i ≠ selected then (C i)ᶜ else univ
  have hO : IsOpen O := by
    apply isOpen_iInter_of_finite
    intro i
    split_ifs
    · exact (hclosed i).isOpen_compl
    · exact isOpen_univ
  have hpO : gamma (if terminal then T - r else r) ∈ O := by
    apply mem_iInter.mpr
    intro i
    by_cases hi : occupied i ∧ i ≠ selected
    · rw [if_pos hi]
      intro hmem
      apply hi.2
      apply m64Intrinsic_corner_cap_tip_unique H hr positive vertical htip F hsector i hi.1
      rwa [haxis]
    · rw [if_neg hi]
      exact mem_univ _
  refine ⟨ell, W0 ∩ O, hW0.inter hO, ⟨hpW0, hpO⟩, hnorm, hker, ?_⟩
  rintro z ⟨⟨hzW, hzO⟩, hzD⟩
  obtain ⟨i, hzD⟩ := mem_iUnion.mp hzD
  obtain ⟨hi, hzC⟩ := mem_iUnion.mp hzD
  have heq : i = selected := by
    by_contra hne
    have hnot := mem_iInter.mp hzO i
    rw [if_pos ⟨hi, hne⟩] at hnot
    exact hnot hzC
  exact hsep z ⟨hzW, heq ▸ hzC⟩

end PoincareConjecture
