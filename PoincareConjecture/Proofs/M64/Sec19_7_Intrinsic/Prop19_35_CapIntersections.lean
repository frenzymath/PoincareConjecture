import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RetainedLoopCaps












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture

private theorem common_sector_mem_axes {i j : Bool × Bool} (hij : i ≠ j)
    {q : ℝ × ℝ}
    (hi : q ∈ (sectorParameterEquiv 0 i) '' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2})
    (hj : q ∈ (sectorParameterEquiv 0 j) '' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}) :
    q.1 = 0 ∨ q.2 = 0 := by
  obtain ⟨p, hp, rfl⟩ := hi
  obtain ⟨w, hw, heq⟩ := hj
  have heq1 := congrArg Prod.fst heq
  have heq2 := congrArg Prod.snd heq
  rcases i with ⟨i, k⟩
  rcases j with ⟨j, l⟩
  cases i <;> cases k <;> cases j <;> cases l <;>
    simp only [sectorParameterEquiv_apply, Bool.false_eq_true, ↓reduceIte]
      at heq1 heq2 ⊢ <;> dsimp at heq1 heq2 ⊢
  all_goals first | exact (hij rfl).elim | (left; linarith [hp.1, hw.1]) |
    (right; linarith [hp.2, hw.2])





theorem m64Intrinsic_cap_inter_eq_common_axes
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) {r : ℝ}
    (C : Bool × Bool → Set AnnulusCoordinates)
    (hsector : ∀ i, C i ⊆ H '' (H.source ∩ (sectorParameterEquiv 0 i) ''
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (haxes : ∀ i, C i ∩ H '' (H.source ∩ {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0}) =
      H '' ((sectorParameterEquiv 0 i) ''
        ((Icc (0 : ℝ) r ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) r))))
    {i j : Bool × Bool} (hij : i ≠ j) :
    C i ∩ C j =
      (H '' ((sectorParameterEquiv 0 i) ''
        ((Icc (0 : ℝ) r ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) r)))) ∩
      (H '' ((sectorParameterEquiv 0 j) ''
        ((Icc (0 : ℝ) r ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) r)))) := by
  ext z
  constructor
  · rintro ⟨hzi, hzj⟩
    obtain ⟨p, hp, hpz⟩ := hsector i hzi
    obtain ⟨q, hq, hqz⟩ := hsector j hzj
    have hpq := H.injOn hp.1 hq.1 (hpz.trans hqz.symm)
    have hpaxes := common_sector_mem_axes hij hp.2 (hpq.symm ▸ hq.2)
    have hzaxes : z ∈ H '' (H.source ∩ {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0}) :=
      ⟨p, ⟨hp.1, hpaxes⟩, hpz⟩
    exact ⟨(haxes i).subset ⟨hzi, hzaxes⟩, (haxes j).subset ⟨hzj, hzaxes⟩⟩
  · rintro ⟨hzi, hzj⟩
    exact ⟨((haxes i).superset hzi).1, ((haxes j).superset hzj).1⟩

private theorem signed_axes_inter_horizontal {r : ℝ} (hr : 0 ≤ r) (i : Bool) :
    ((sectorParameterEquiv 0 (i, false)) ''
      ((Icc (0 : ℝ) r ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) r))) ∩
    ((sectorParameterEquiv 0 (i, true)) ''
      ((Icc (0 : ℝ) r ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) r))) =
    (sectorParameterEquiv 0 (i, false)) '' (Icc (0 : ℝ) r ×ˢ {0}) := by
  ext q
  constructor
  · rintro ⟨⟨p, hp, hpq⟩, ⟨w, hw, hwq⟩⟩
    rcases hp with hp | hp
    · exact ⟨p, hp, hpq⟩
    · have hp0 : p.1 = 0 := hp.1
      have hpfirst : p.1 ∈ Icc (0 : ℝ) r := by
        rw [hp0]
        exact ⟨le_rfl, hr⟩
      rcases hw with hw | hw
      · have hp2 : p.2 = 0 := by
          have heq := congrArg Prod.snd (hpq.trans hwq.symm)
          simp [sectorParameterEquiv_apply] at heq
          linarith [show w.2 = 0 from hw.2]
        exact ⟨p, ⟨hpfirst, hp2⟩, hpq⟩
      · have hp2 : p.2 = 0 := by
          have heq := congrArg Prod.snd (hpq.trans hwq.symm)
          simp [sectorParameterEquiv_apply] at heq
          linarith [hp.2.1, hw.2.1]
        exact ⟨p, ⟨hpfirst, hp2⟩, hpq⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨⟨p, Or.inl hp, rfl⟩, ⟨p, Or.inl hp, ?_⟩⟩
    have hp0 : p.2 = 0 := hp.2
    simp [sectorParameterEquiv_apply, hp0]





theorem m64Intrinsic_neighbor_caps_inter_horizontal
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) {r : ℝ} (hr : 0 ≤ r)
    (C : Bool × Bool → Set AnnulusCoordinates)
    (hsector : ∀ i, C i ⊆ H '' (H.source ∩ (sectorParameterEquiv 0 i) ''
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (haxes : ∀ i, C i ∩ H '' (H.source ∩ {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0}) =
      H '' ((sectorParameterEquiv 0 i) ''
        ((Icc (0 : ℝ) r ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) r))))
    (hsmall : ∀ i : Bool × Bool, ∀ s ∈ Icc (0 : ℝ) r,
      sectorParameterEquiv 0 i (s, 0) ∈ H.source ∧
      sectorParameterEquiv 0 i (0, s) ∈ H.source) (i : Bool) :
    C (i, false) ∩ C (i, true) =
      H '' ((sectorParameterEquiv 0 (i, false)) '' (Icc (0 : ℝ) r ×ˢ {0})) := by
  have hsource (j : Bool × Bool) :
      (sectorParameterEquiv 0 j) ''
        ((Icc (0 : ℝ) r ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) r)) ⊆ H.source := by
    rintro _ ⟨p, hp, rfl⟩
    rcases hp with hp | hp
    · have heq : p = (p.1, 0) := Prod.ext rfl hp.2
      rw [heq]
      exact (hsmall j p.1 hp.1).1
    · have heq : p = (0, p.2) := Prod.ext hp.1 rfl
      rw [heq]
      exact (hsmall j p.2 hp.2).2
  rw [m64Intrinsic_cap_inter_eq_common_axes H C hsector haxes (by simp),
    ← Set.InjOn.image_inter H.injOn (hsource _) (hsource _),
    signed_axes_inter_horizontal hr i]

private theorem signed_axes_inter_vertical {r : ℝ} (hr : 0 ≤ r) (j : Bool) :
    ((sectorParameterEquiv 0 (false, j)) ''
      ((Icc (0 : ℝ) r ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) r))) ∩
    ((sectorParameterEquiv 0 (true, j)) ''
      ((Icc (0 : ℝ) r ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) r))) =
    (sectorParameterEquiv 0 (false, j)) '' ({0} ×ˢ Icc (0 : ℝ) r) := by
  ext q
  constructor
  · rintro ⟨⟨p, hp, hpq⟩, ⟨w, hw, hwq⟩⟩
    rcases hp with hp | hp
    · have hp0 : p.2 = 0 := hp.2
      have hpsecond : p.2 ∈ Icc (0 : ℝ) r := by
        rw [hp0]
        exact ⟨le_rfl, hr⟩
      rcases hw with hw | hw
      · have hp1 : p.1 = 0 := by
          have heq := congrArg Prod.fst (hpq.trans hwq.symm)
          simp [sectorParameterEquiv_apply] at heq
          linarith [hp.1.1, hw.1.1]
        exact ⟨p, ⟨hp1, hpsecond⟩, hpq⟩
      · have hp1 : p.1 = 0 := by
          have heq := congrArg Prod.fst (hpq.trans hwq.symm)
          simp [sectorParameterEquiv_apply] at heq
          linarith [show w.1 = 0 from hw.1]
        exact ⟨p, ⟨hp1, hpsecond⟩, hpq⟩
    · exact ⟨p, hp, hpq⟩
  · rintro ⟨p, hp, rfl⟩
    refine ⟨⟨p, Or.inr hp, rfl⟩, ⟨p, Or.inr hp, ?_⟩⟩
    have hp0 : p.1 = 0 := hp.1
    simp [sectorParameterEquiv_apply, hp0]





theorem m64Intrinsic_neighbor_caps_inter_vertical
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) {r : ℝ} (hr : 0 ≤ r)
    (C : Bool × Bool → Set AnnulusCoordinates)
    (hsector : ∀ i, C i ⊆ H '' (H.source ∩ (sectorParameterEquiv 0 i) ''
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (haxes : ∀ i, C i ∩ H '' (H.source ∩ {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0}) =
      H '' ((sectorParameterEquiv 0 i) ''
        ((Icc (0 : ℝ) r ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) r))))
    (hsmall : ∀ i : Bool × Bool, ∀ s ∈ Icc (0 : ℝ) r,
      sectorParameterEquiv 0 i (s, 0) ∈ H.source ∧
      sectorParameterEquiv 0 i (0, s) ∈ H.source) (j : Bool) :
    C (false, j) ∩ C (true, j) =
      H '' ((sectorParameterEquiv 0 (false, j)) '' ({0} ×ˢ Icc (0 : ℝ) r)) := by
  have hsource (i : Bool × Bool) :
      (sectorParameterEquiv 0 i) ''
        ((Icc (0 : ℝ) r ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) r)) ⊆ H.source := by
    rintro _ ⟨p, hp, rfl⟩
    rcases hp with hp | hp
    · have heq : p = (p.1, 0) := Prod.ext rfl hp.2
      rw [heq]
      exact (hsmall i p.1 hp.1).1
    · have heq : p = (0, p.2) := Prod.ext hp.1 rfl
      rw [heq]
      exact (hsmall i p.2 hp.2).2
  rw [m64Intrinsic_cap_inter_eq_common_axes H C hsector haxes (by simp),
    ← Set.InjOn.image_inter H.injOn (hsource _) (hsource _),
    signed_axes_inter_vertical hr j]

private theorem common_opposite_sector_eq_zero {i : Bool × Bool} {q : ℝ × ℝ}
    (hi : q ∈ (sectorParameterEquiv 0 i) '' {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2})
    (hj : q ∈ (sectorParameterEquiv 0 (!i.1, !i.2)) ''
      {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2}) : q = 0 := by
  obtain ⟨p, hp, rfl⟩ := hi
  obtain ⟨w, hw, heq⟩ := hj
  have heq1 := congrArg Prod.fst heq
  have heq2 := congrArg Prod.snd heq
  rcases i with ⟨i, j⟩
  cases i <;> cases j <;> apply Prod.ext <;>
    simp only [sectorParameterEquiv_apply, Bool.not_false, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte] at heq1 heq2 ⊢ <;> dsimp at heq1 heq2 ⊢ <;>
    linarith [hp.1, hp.2, hw.1, hw.2]




theorem m64Intrinsic_opposite_caps_inter
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) {r : ℝ} (hr : 0 ≤ r)
    (C : Bool × Bool → Set AnnulusCoordinates)
    (hsector : ∀ i, C i ⊆ H '' (H.source ∩ (sectorParameterEquiv 0 i) ''
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (haxes : ∀ i, C i ∩ H '' (H.source ∩ {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0}) =
      H '' ((sectorParameterEquiv 0 i) ''
        ((Icc (0 : ℝ) r ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) r)))) (i : Bool × Bool) :
    C i ∩ C (!i.1, !i.2) = {H 0} := by
  have hbase (j : Bool × Bool) : H 0 ∈ C j := by
    apply ((haxes j).superset ?_).1
    refine ⟨0, ⟨0, Or.inl ⟨⟨le_rfl, hr⟩, rfl⟩, ?_⟩, rfl⟩
    exact sectorParameterEquiv_zero 0 j
  ext z
  constructor
  · rintro ⟨hzi, hzj⟩
    obtain ⟨p, hp, hpz⟩ := hsector i hzi
    obtain ⟨q, hq, hqz⟩ := hsector (!i.1, !i.2) hzj
    have hpq := H.injOn hp.1 hq.1 (hpz.trans hqz.symm)
    have hp0 := common_opposite_sector_eq_zero hp.2 (hpq.symm ▸ hq.2)
    exact (hpz.symm.trans (congrArg H hp0) : z = H 0)
  · rintro rfl
    exact ⟨hbase i, hbase _⟩

end PoincareConjecture
