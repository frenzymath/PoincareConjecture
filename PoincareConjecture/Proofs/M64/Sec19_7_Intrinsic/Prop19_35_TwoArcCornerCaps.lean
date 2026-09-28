import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ExactTwoArcCorner












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture





theorem m64Intrinsic_exists_two_arc_corner_caps
    {alpha beta : ℝ → AnnulusCoordinates} (ha : ContDiff ℝ ∞ alpha)
    (hb : ContDiff ℝ ∞ beta) {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (hai : InjOn alpha (Icc 0 A)) (hbi : InjOn beta (Icc 0 B))
    (hbase : beta 0 = alpha 0)
    (hind : LinearIndependent ℝ
      (![deriv alpha 0, deriv beta 0] : Fin 2 → AnnulusCoordinates))
    {K U V O : Set AnnulusCoordinates} (hK : IsCompact K) (hpK : alpha 0 ∉ K)
    (hU : IsOpen U) (hV : IsOpen V) (hdisj : Disjoint U V)
    (hfU : frontier U = alpha '' Icc 0 A ∪ beta '' Icc 0 B ∪ K)
    (hfV : frontier V = frontier U) (hO : IsOpen O) (hpO : alpha 0 ∈ O) :
    ∃ (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) (r : ℝ)
      (F : Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
      (W : Set AnnulusCoordinates) (positive : Bool),
      let C (i : Bool × Bool) :=
        F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
      let D := ⋃ i, ⋃ (_ : if positive then i = (true, true) else i ≠ (true, true)), C i
      0 < r ∧ r ≤ min A B / 3 ∧ (0 : ℝ × ℝ) ∈ H.source ∧ H 0 = alpha 0 ∧
      H.target ⊆ O ∧ ContDiffOn ℝ ∞ H H.source ∧ ContDiffOn ℝ ∞ H.symm H.target ∧
      (∀ s : ℝ, H (s, 0) = alpha s) ∧ (∀ s : ℝ, H (0, s) = beta s) ∧
      (∀ i : Bool × Bool, ∀ s ∈ Icc (0 : ℝ) r,
        sectorParameterEquiv 0 i (s, 0) ∈ H.source ∧
        sectorParameterEquiv 0 i (0, s) ∈ H.source) ∧
      (∀ q ∈ H.source, H q ∈ frontier U ↔
        (q.1 = 0 ∧ 0 ≤ q.2) ∨ (0 ≤ q.1 ∧ q.2 = 0)) ∧
      (∀ q ∈ H.source, H q ∈ closure U ↔
        if positive then 0 ≤ q.1 ∧ 0 ≤ q.2 else q.1 ≤ 0 ∨ q.2 ≤ 0) ∧
      (∀ i,
        {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r} ⊆ (F i).source ∧
        (F i).target ⊆ H.target ∧
        ContDiffOn ℝ ∞ (F i) (F i).source ∧
        ContDiffOn ℝ ∞ (F i).symm (F i).target ∧
        (∀ s ∈ Icc (0 : ℝ) r, F i (s, 0) = H (sectorParameterEquiv 0 i (s, 0))) ∧
        (∀ s ∈ Icc (0 : ℝ) r, F i (0, s) = H (sectorParameterEquiv 0 i (0, s))) ∧
        (∀ t : ℝ, F i ((1 - t) * r, t * r) =
          (1 - t) • F i (r, 0) + t • F i (0, r)) ∧
        C i ⊆ H '' (H.source ∩ (sectorParameterEquiv 0 i) ''
          {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}) ∧
        C i ∩ H '' (H.source ∩ {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0}) =
          H '' ((sectorParameterEquiv 0 i) ''
            ((Icc (0 : ℝ) r ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) r)))) ∧
      IsOpen W ∧ alpha 0 ∈ W ∧ D ⊆ O ∧ D ⊆ closure U ∧ W ∩ closure U ⊆ D ∧
      D ∩ frontier U = alpha '' Icc 0 r ∪ beta '' Icc 0 r := by
  classical
  obtain ⟨H, h0, hpoint, htarget, hH, hHi, haxis, haxis', hfront, hside⟩ :=
    m64Intrinsic_exists_exact_two_arc_corner_region ha hb hA hB hai hbi hbase hind
      hK hpK hU hV hdisj hfU hfV hO hpO
  obtain ⟨eta, heta, hball⟩ := Metric.mem_nhds_iff.mp (H.open_source.mem_nhds h0)
  have hmin : 0 < min A B / 3 := div_pos (lt_min hA hB) (by norm_num)
  obtain ⟨r, F, W, hr, hrbound, hW, hpW, hWt, hF⟩ :=
    m64Intrinsic_exists_four_axis_fitted_caps H h0 hH hHi (lt_min hmin (half_pos heta))
  have hrAB : r ≤ min A B / 3 := hrbound.trans (min_le_left _ _)
  have hrA : r ≤ A := by have h := min_le_left A B; linarith
  have hrB : r ≤ B := by have h := min_le_right A B; linarith
  have hre : r < eta := (hrbound.trans (min_le_right _ _)).trans_lt (half_lt_self heta)
  have hsmall (i : Bool × Bool) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) r) (vertical : Bool) :
      sectorParameterEquiv 0 i (if vertical then (0, s) else (s, 0)) ∈ H.source := by
    apply hball
    rcases i with ⟨i, j⟩
    cases i <;> cases j <;> cases vertical <;>
      simp [sectorParameterEquiv_apply, Metric.mem_ball,
        abs_of_nonneg hs.1, hs.2.trans_lt hre, heta]
  obtain ⟨positive, hside'⟩ : ∃ positive : Bool, ∀ q ∈ H.source,
      H q ∈ closure U ↔ if positive then 0 ≤ q.1 ∧ 0 ≤ q.2 else q.1 ≤ 0 ∨ q.2 ≤ 0 := by
    rcases hside with hpos | hneg
    · exact ⟨true, hpos⟩
    · exact ⟨false, hneg⟩
  let C (i : Bool × Bool) :=
    F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
  let occupied (i : Bool × Bool) := if positive then i = (true, true) else i ≠ (true, true)
  let D := ⋃ i, ⋃ (_ : occupied i), C i
  have hcap (i : Bool × Bool) := (hF i).2.2.2.2.2.2.2.1
  have hcontacts (i : Bool × Bool) := (hF i).2.2.2.2.2.2.2.2.1
  have hcover (i : Bool × Bool) := (hF i).2.2.2.2.2.2.2.2.2
  have hcontact (i : Bool × Bool) : C i ∩ frontier U ⊆
      alpha '' Icc 0 r ∪ beta '' Icc 0 r := by
    intro z hz
    have hzt : z ∈ H.target := by
      obtain ⟨q, hq, rfl⟩ := hz.1
      exact (hF i).2.1 ((F i).map_source ((hF i).1 hq))
    have hq := H.map_target hzt
    have hqfront := (hfront (H.symm z) hq).mp (by simpa only [H.right_inv hzt] using hz.2)
    have hzaxes : z ∈ H '' (H.source ∩ {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0}) := by
      refine ⟨H.symm z, ⟨hq, ?_⟩, H.right_inv hzt⟩
      exact hqfront.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
    obtain ⟨_, ⟨p, hp, rfl⟩, hpz⟩ := (hcontacts i).subset ⟨hz.1, hzaxes⟩
    rcases hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
    · have hp : p = (p.1, 0) := Prod.ext rfl hp2
      rw [hp] at hpz
      have hsfront := (hfront _ (hsmall i hp1 false)).mp (hpz.symm ▸ hz.2)
      rcases i with ⟨i, j⟩
      cases i
      · have hs0 : p.1 = 0 := by
          simp only [sectorParameterEquiv_apply] at hsfront
          rcases hsfront with hs | hs <;> dsimp at hs <;> linarith [hp1.1]
        exact Or.inl ⟨0, ⟨le_rfl, hr.le⟩,
          by simpa [sectorParameterEquiv_apply, hs0, haxis] using hpz⟩
      · exact Or.inl ⟨p.1, hp1, by simpa [sectorParameterEquiv_apply, haxis] using hpz⟩
    · have hp : p = (0, p.2) := Prod.ext hp1 rfl
      rw [hp] at hpz
      have hsfront := (hfront _ (hsmall i hp2 true)).mp (hpz.symm ▸ hz.2)
      rcases i with ⟨i, j⟩
      cases j
      · have hs0 : p.2 = 0 := by
          simp only [sectorParameterEquiv_apply] at hsfront
          rcases hsfront with hs | hs <;> dsimp at hs <;> linarith [hp2.1]
        exact Or.inr ⟨0, ⟨le_rfl, hr.le⟩,
          by simpa [sectorParameterEquiv_apply, hs0, haxis'] using hpz⟩
      · exact Or.inr ⟨p.2, hp2, by simpa [sectorParameterEquiv_apply, haxis'] using hpz⟩
  have hsub : D ⊆ closure U := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    obtain ⟨hoccupied, hz⟩ := mem_iUnion.mp hi
    obtain ⟨_, ⟨hq, p, hp, rfl⟩, rfl⟩ := hcap i hz
    apply (hside' _ hq).mpr
    cases positive
    · rcases i with ⟨i, j⟩
      cases i <;> cases j <;> simp_all [occupied, sectorParameterEquiv_apply]
    · have hi' : i = (true, true) := hoccupied
      simp [hi', sectorParameterEquiv_apply, hp.1, hp.2]
  have hcovered : W ∩ closure U ⊆ D := by
    intro z hz
    have hzt := hWt hz.1
    let q := H.symm z
    have hq : q ∈ H.source := H.map_target hzt
    have hqz : H q = z := H.right_inv hzt
    have hqside := (hside' q hq).mp (hqz.symm ▸ hz.2)
    have hmember (i : Bool × Bool) (hi : occupied i) (p : ℝ × ℝ)
        (hp : 0 ≤ p.1 ∧ 0 ≤ p.2) (heq : sectorParameterEquiv 0 i p = q) : z ∈ D :=
      mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi,
        hcover i ⟨hz.1, q, ⟨hq, p, hp, heq⟩, hqz⟩⟩⟩
    cases positive
    · by_cases hq1 : q.1 ≤ 0
      · by_cases hq2 : q.2 ≤ 0
        · exact hmember (false, false) (by simp [occupied]) (-q.1, -q.2)
            ⟨neg_nonneg.mpr hq1, neg_nonneg.mpr hq2⟩ (by simp [sectorParameterEquiv_apply])
        · exact hmember (false, true) (by simp [occupied]) (-q.1, q.2)
            ⟨neg_nonneg.mpr hq1, (lt_of_not_ge hq2).le⟩ (by simp [sectorParameterEquiv_apply])
      · have hq2 : q.2 ≤ 0 := hqside.resolve_left hq1
        exact hmember (true, false) (by simp [occupied]) (q.1, -q.2)
          ⟨(lt_of_not_ge hq1).le, neg_nonneg.mpr hq2⟩ (by simp [sectorParameterEquiv_apply])
    · exact hmember (true, true) (by simp [occupied]) q hqside
        (by simp [sectorParameterEquiv_apply])
  refine ⟨H, r, F, W, positive, hr, hrAB, h0, hpoint, htarget, hH, hHi, haxis, haxis',
    fun i s hs => ⟨hsmall i hs false, hsmall i hs true⟩, hfront, hside', ?_, hW,
    hpoint ▸ hpW, ?_, hsub, hcovered, ?_⟩
  · intro i
    exact ⟨(hF i).1, (hF i).2.1, (hF i).2.2.1, (hF i).2.2.2.1,
      (hF i).2.2.2.2.1, (hF i).2.2.2.2.2.1, (hF i).2.2.2.2.2.2.1,
      hcap i, hcontacts i⟩
  · rintro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp hz
    obtain ⟨_, q, hq, rfl⟩ := mem_iUnion.mp hi
    exact htarget ((hF i).2.1 ((F i).map_source ((hF i).1 hq)))
  · ext z
    constructor
    · rintro ⟨hz, hzf⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      obtain ⟨_, hz⟩ := mem_iUnion.mp hi
      exact hcontact i ⟨hz, hzf⟩
    · intro hz
      constructor
      · rcases hz with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
        · apply mem_iUnion.mpr
          refine ⟨(true, positive), mem_iUnion.mpr ⟨?_, ?_⟩⟩
          · cases positive <;> simp
          · refine ⟨(s, 0), ⟨hs.1, le_rfl, by simpa using hs.2⟩, ?_⟩
            simpa [sectorParameterEquiv_apply, haxis] using (hF (true, positive)).2.2.2.2.1 s hs
        · apply mem_iUnion.mpr
          refine ⟨(positive, true), mem_iUnion.mpr ⟨?_, ?_⟩⟩
          · cases positive <;> simp
          · refine ⟨(0, s), ⟨le_rfl, hs.1, by simpa using hs.2⟩, ?_⟩
            simpa [sectorParameterEquiv_apply, haxis'] using (hF (positive, true)).2.2.2.2.2.1 s hs
      · rw [hfU]
        rcases hz with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
        · exact Or.inl (Or.inl ⟨s, ⟨hs.1, hs.2.trans hrA⟩, rfl⟩)
        · exact Or.inl (Or.inr ⟨s, ⟨hs.1, hs.2.trans hrB⟩, rfl⟩)

end PoincareConjecture
