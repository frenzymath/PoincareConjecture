import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_ExactCornerRegion

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology ContDiff Manifold Matrix
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture

theorem m64Intrinsic_exists_loop_caps_with_exact_contacts
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {T : ℝ} (hT : 0 < T)
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hind : LinearIndependent ℝ
      (![deriv gamma 0, -deriv gamma T] : Fin 2 → AnnulusCoordinates))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfU : frontier U = gamma '' Icc 0 T)
    (hfV : frontier V = gamma '' Icc 0 T) :
    ∃ (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) (r : ℝ)
      (F : Bool × Bool → OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates)
      (W : Set AnnulusCoordinates) (positive : Bool),
      let C (i : Bool × Bool) :=
        F i '' {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ r}
      let occupied (i : Bool × Bool) := if positive then i = (true, true) else i ≠ (true, true)
      let A := ⋃ i, ⋃ (_ : occupied i), C i
      0 < r ∧ r ≤ T / 3 ∧ H 0 = gamma 0 ∧
      (∀ s : ℝ, H (s, 0) = gamma s) ∧
      (∀ s : ℝ, H (0, s) = gamma (T - s)) ∧
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
          {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2})) ∧
      IsOpen W ∧ gamma 0 ∈ W ∧ A ⊆ closure U ∧ W ∩ closure U ⊆ A ∧
      A ∩ gamma '' Icc 0 T = gamma '' Icc 0 r ∪ gamma '' Icc (T - r) T := by
  classical
  obtain ⟨H, h0, hbase, hH, hHi, haxis, haxis', hloop, hside⟩ :=
    m64Intrinsic_exists_exact_loop_corner_region hg hT hend hinj hind hU hV hdisj hfU hfV
  obtain ⟨eta, heta, hball⟩ := Metric.mem_nhds_iff.mp (H.open_source.mem_nhds h0)
  obtain ⟨r, F, W, hr, hrbound, hW, hpW, hWt, hF⟩ :=
    m64Intrinsic_exists_four_axis_fitted_caps H h0 hH hHi
      (lt_min (show (0 : ℝ) < T / 3 by positivity) (half_pos heta))
  have hrT : r ≤ T / 3 := hrbound.trans (min_le_left _ _)
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
  let A := ⋃ i, ⋃ (_ : occupied i), C i
  have hcap (i : Bool × Bool) := (hF i).2.2.2.2.2.2.2.1
  have hcontacts (i : Bool × Bool) := (hF i).2.2.2.2.2.2.2.2.1
  have hcover (i : Bool × Bool) := (hF i).2.2.2.2.2.2.2.2.2
  have hcontact (i : Bool × Bool) : C i ∩ gamma '' Icc 0 T ⊆
      gamma '' Icc 0 r ∪ gamma '' Icc (T - r) T := by
    intro z hz
    have hzt : z ∈ H.target := by
      obtain ⟨q, hq, rfl⟩ := hz.1
      exact (hF i).2.1 ((F i).map_source ((hF i).1 hq))
    have hq := H.map_target hzt
    have hqloop := (hloop (H.symm z) hq).mp (by simpa only [H.right_inv hzt] using hz.2)
    have hzaxes : z ∈ H '' (H.source ∩ {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0}) := by
      refine ⟨H.symm z, ⟨hq, ?_⟩, H.right_inv hzt⟩
      exact hqloop.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
    have hzsmall := (hcontacts i).subset ⟨hz.1, hzaxes⟩
    obtain ⟨_, ⟨p, hp, rfl⟩, hpz⟩ := hzsmall
    rcases hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
    · have hp : p = (p.1, 0) := Prod.ext rfl hp2
      rw [hp] at hpz
      have hsloop := (hloop _ (hsmall i hp1 false)).mp (hpz.symm ▸ hz.2)
      rcases i with ⟨i, j⟩
      cases i
      · have hs0 : p.1 = 0 := by
          simp only [sectorParameterEquiv_apply] at hsloop
          rcases hsloop with hs | hs <;> dsimp at hs <;> linarith [hp1.1]
        apply Or.inl
        refine ⟨0, ⟨le_rfl, hr.le⟩, ?_⟩
        simpa [sectorParameterEquiv_apply, hs0, haxis] using hpz
      · apply Or.inl
        exact ⟨p.1, hp1, by simpa [sectorParameterEquiv_apply, haxis] using hpz⟩
    · have hp : p = (0, p.2) := Prod.ext hp1 rfl
      rw [hp] at hpz
      have hsloop := (hloop _ (hsmall i hp2 true)).mp (hpz.symm ▸ hz.2)
      rcases i with ⟨i, j⟩
      cases j
      · have hs0 : p.2 = 0 := by
          simp only [sectorParameterEquiv_apply] at hsloop
          rcases hsloop with hs | hs <;> dsimp at hs <;> linarith [hp2.1]
        apply Or.inl
        refine ⟨0, ⟨le_rfl, hr.le⟩, ?_⟩
        simpa [sectorParameterEquiv_apply, hs0, haxis] using hpz
      · apply Or.inr
        exact ⟨T - p.2, ⟨by linarith [hp2.2], by linarith [hp2.1]⟩,
          by simpa [sectorParameterEquiv_apply, haxis'] using hpz⟩
  have hsub : A ⊆ closure U := by
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
  have hcovered : W ∩ closure U ⊆ A := by
    intro z hz
    have hzt := hWt hz.1
    let q := H.symm z
    have hq : q ∈ H.source := H.map_target hzt
    have hqz : H q = z := H.right_inv hzt
    have hqside := (hside' q hq).mp (hqz.symm ▸ hz.2)
    have hmember (i : Bool × Bool) (hi : occupied i) (p : ℝ × ℝ)
        (hp : 0 ≤ p.1 ∧ 0 ≤ p.2) (heq : sectorParameterEquiv 0 i p = q) : z ∈ A :=
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
  refine ⟨H, r, F, W, positive, hr, hrT, hbase, haxis, haxis', ?_, hW,
    hbase ▸ hpW, hsub, hcovered, ?_⟩
  · intro i
    exact ⟨(hF i).1, (hF i).2.1, (hF i).2.2.1, (hF i).2.2.2.1,
      (hF i).2.2.2.2.1, (hF i).2.2.2.2.2.1, (hF i).2.2.2.2.2.2.1, hcap i⟩
  · ext z
    constructor
    · rintro ⟨hz, hzloop⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      obtain ⟨_, hz⟩ := mem_iUnion.mp hi
      exact hcontact i ⟨hz, hzloop⟩
    · intro hz
      constructor
      · rcases hz with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
        · apply mem_iUnion.mpr
          refine ⟨(true, positive), mem_iUnion.mpr ⟨?_, ?_⟩⟩
          · cases positive <;> simp
          · refine ⟨(s, 0), ⟨hs.1, le_rfl, by simpa using hs.2⟩, ?_⟩
            simpa [sectorParameterEquiv_apply, haxis] using (hF (true, positive)).2.2.2.2.1 s hs
        · have hs' : T - s ∈ Icc (0 : ℝ) r := ⟨by linarith [hs.2], by linarith [hs.1]⟩
          apply mem_iUnion.mpr
          refine ⟨(positive, true), mem_iUnion.mpr ⟨?_, ?_⟩⟩
          · cases positive <;> simp
          · refine ⟨(0, T - s), ⟨le_rfl, hs'.1, by simpa using hs'.2⟩, ?_⟩
            simpa [sectorParameterEquiv_apply, haxis'] using
              (hF (positive, true)).2.2.2.2.2.1 (T - s) hs'
      · rcases hz with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
        · exact ⟨s, ⟨hs.1, by linarith [hs.2]⟩, rfl⟩
        · exact ⟨s, ⟨by linarith [hs.1], hs.2⟩, rfl⟩

end PoincareConjecture
