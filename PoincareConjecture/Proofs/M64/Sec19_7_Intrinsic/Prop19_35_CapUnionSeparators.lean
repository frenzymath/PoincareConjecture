import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_LoopCapTips
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapEndpointSeparator












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture




theorem m64Intrinsic_cap_isCompact
    (F : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) {r : ℝ}
    (hsource : {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ F.source) :
    IsCompact (F '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}) := by
  have hclosed : IsClosed {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
  have hsub : {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆
      Icc (0 : ℝ) r ×ˢ Icc (0 : ℝ) r := by
    intro q hq
    exact ⟨⟨hq.1, by linarith [hq.2.1, hq.2.2]⟩,
      ⟨hq.2.1, by linarith [hq.1, hq.2.2]⟩⟩
  exact ((isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hclosed hsub).image_of_continuousOn
    (F.continuousOn.mono hsource)





theorem m64Intrinsic_exists_loop_cap_union_separator
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma)
    {T r : ℝ} (hr : 0 < r) (hrT : r < T) (hinj : InjOn gamma (Ico 0 T))
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) (hbase : H 0 = gamma 0)
    (haxis : ∀ s : ℝ, H (s, 0) = gamma s)
    (haxis' : ∀ s : ℝ, H (0, s) = gamma (T - s))
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
    (positive terminal : Bool) :
    let selected := if terminal then (positive, true) else (true, positive)
    let occupied (i : Bool × Bool) := if positive then i = (true, true) else i ≠ (true, true)
    let A := ⋃ i, ⋃ (_ : occupied i),
      F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
    ∃ (ell : AnnulusCoordinates →L[ℝ] ℝ) (W : Set AnnulusCoordinates),
      IsOpen W ∧ gamma (if terminal then T - r else r) ∈ W ∧
      ell (deriv gamma (if terminal then T - r else r)) = (if terminal then -1 else 1) ∧
      ell (if terminal then F selected (r, 0) - F selected (0, r)
        else F selected (0, r) - F selected (r, 0)) = 0 ∧
      ∀ z ∈ W ∩ A, ell (z - gamma (if terminal then T - r else r)) ≤ 0 := by
  classical
  let selected := if terminal then (positive, true) else (true, positive)
  let occupied (i : Bool × Bool) := if positive then i = (true, true) else i ≠ (true, true)
  let C (i : Bool × Bool) :=
    F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
  have hclosed (i : Bool × Bool) : IsClosed (C i) :=
    (m64Intrinsic_cap_isCompact (F i) (hsource i)).isClosed
  have hselected : ∀ s ∈ Icc (0 : ℝ) r,
      F selected (if terminal then (0, s) else (s, 0)) =
        gamma (if terminal then T - s else s) := by
    intro s hs
    cases terminal
    · simpa [selected, sectorParameterEquiv_apply, haxis] using hfirst (true, positive) s hs
    · simpa [selected, sectorParameterEquiv_apply, haxis'] using hsecond (positive, true) s hs
  obtain ⟨ell, W0, hW0, hpW0, hnorm, hker, hsep⟩ :=
    m64Intrinsic_exists_cap_endpoint_separator hg hr (F selected) (hsource selected)
      (hF selected) (hFi selected) (hchord selected) terminal terminal hselected
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
      exact hi.2 (m64Intrinsic_loop_cap_tip_unique hr hrT hinj H hbase haxis haxis'
        F hfirst hsecond hsector positive terminal i hi.1 hmem)
    · rw [if_neg hi]
      exact mem_univ _
  refine ⟨ell, W0 ∩ O, hW0.inter hO, ⟨hpW0, hpO⟩, hnorm, hker, ?_⟩
  rintro z ⟨⟨hzW, hzO⟩, hzA⟩
  obtain ⟨i, hzA⟩ := mem_iUnion.mp hzA
  obtain ⟨hi, hzC⟩ := mem_iUnion.mp hzA
  have heq : i = selected := by
    by_contra hne
    have hnot := mem_iInter.mp hzO i
    rw [if_pos ⟨hi, hne⟩] at hnot
    exact hnot hzC
  apply hsep z
  exact ⟨hzW, heq ▸ hzC⟩

end PoincareConjecture
