import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.NativeLevelGeometry

set_option autoImplicit false

open Set
open scoped Matrix

namespace PoincareConjecture.M25.Topology3D

theorem exists_saddle_nested_reference_inner_connector_incidence
    (e : OpenPartialHomeomorph UnitTwoSphere (ℝ × ℝ))
    (k d rho delta : ℝ)
    (hrho : 0 < rho) (hdelta : 0 < delta) (hsmall : delta < rho ^ 2)
    (hdisc : {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2} ⊆ e.target)
    (hheight : ∀ p ∈ e.source,
      (heightCoordinates (nestedReferenceDiffeomorph d (p : E3))).2 =
        k + d - (e p).1 ^ 2 + (e p).2 ^ 2)
    (q : Fin 2 → UnitCircle → UnitTwoSphere)
    (hq : ∀ i : Fin 2, Continuous (q i))
    (hqd : Disjoint (range (q 0)) (range (q 1))) :
    let La : Set UnitTwoSphere := {p |
      (heightCoordinates (nestedReferenceDiffeomorph d (p : E3))).2 = k + d - delta}
    let Dc : Set UnitTwoSphere := e.symm ''
      {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2}
    let aa : ℝ := Real.sqrt ((rho ^ 2 - delta) / 2)
    let sg : Fin 2 → ℝ := ![1, -1]
    let v : unitInterval → ℝ := fun t => aa * (1 - 2 * (t : ℝ))
    let gamma : ℝ → Fin 2 → unitInterval → UnitTwoSphere := fun sigma i t =>
      e.symm (sigma * sg i * Real.sqrt ((v t) ^ 2 + delta), sigma * sg i * v t)
    let other : Fin 2 → Fin 2 := fun i => if i = 0 then 1 else 0
    (⋃ i : Fin 2, range (q i)) = La →
    (∀ B : Set UnitTwoSphere, B ⊆ La → IsCompact B →
      IsCompact (La \ B) → Disjoint B Dc → B = ∅) →
    ∃ iPos : Fin 2,
      (iPos = 0 ↔ e.symm (Real.sqrt delta, 0) ∈ range (q 0)) ∧
      (iPos = 1 ↔ e.symm (-Real.sqrt delta, 0) ∈ range (q 0)) ∧
      let iRef : ℝ → Fin 2 := fun sigma => if sigma = 1 then iPos else other iPos
      iRef (-1) = other (iRef 1) ∧
      (∀ sigma : ℝ, sigma = 1 ∨ sigma = -1 →
        range (q 0) ∩ Dc = range (gamma sigma (iRef sigma)) ∧
        range (q 1) ∩ Dc = range (gamma sigma (other (iRef sigma)))) ∧
      ∀ iTar : Fin 2,
        let sigma : ℝ := if iPos = iTar then 1 else -1
        (sigma = 1 ∨ sigma = -1) ∧ iRef sigma = iTar ∧
        ∀ label : Fin 2 ≃ Fin 2,
          (∀ i : Fin 2, range (gamma sigma i) ⊆ range (q (label i))) →
          label.symm 0 = iTar := by
  classical
  dsimp only
  intro hlevel hNoBypass
  let La : Set UnitTwoSphere := {p |
    (heightCoordinates (nestedReferenceDiffeomorph d (p : E3))).2 = k + d - delta}
  let Dc : Set UnitTwoSphere := e.symm ''
    {s : ℝ × ℝ | s.1 ^ 2 + s.2 ^ 2 ≤ rho ^ 2}
  let aa : ℝ := Real.sqrt ((rho ^ 2 - delta) / 2)
  let sg : Fin 2 → ℝ := ![1, -1]
  let v : unitInterval → ℝ := fun t => aa * (1 - 2 * (t : ℝ))
  let gamma : ℝ → Fin 2 → unitInterval → UnitTwoSphere := fun sigma i t =>
    e.symm (sigma * sg i * Real.sqrt ((v t) ^ 2 + delta), sigma * sg i * v t)
  let other : Fin 2 → Fin 2 := fun i => if i = 0 then 1 else 0
  have hlevel' : (⋃ i : Fin 2, range (q i)) = La := by
    simpa [La] using hlevel
  have hheight' : ∀ p ∈ e.source,
      (heightCoordinates (nestedReferenceDiffeomorph d (p : E3))).2 =
        k + d - (e p).1 ^ 2 + (e p).2 ^ 2 := hheight
  have hplus := saddle_nested_reference_lower_connectors e k d rho delta 1
      hrho hdelta hsmall (Or.inl rfl) hdisc hheight'
  have hminus := saddle_nested_reference_lower_connectors e k d rho delta (-1)
      hrho hdelta hsmall (Or.inr rfl) hdisc hheight'
  rcases hplus with ⟨hplusCont, hplusDis, hplusEnd, hplusClosed, hplusOpen⟩
  rcases hminus with ⟨hminusCont, hminusDis, hminusEnd, hminusClosed, hminusOpen⟩
  have hplusCont' : ∀ i : Fin 2,
      Continuous (gamma 1 i) ∧ Function.Injective (gamma 1 i) := by
    simpa [gamma, v, aa, sg] using hplusCont
  have hminusCont' : ∀ i : Fin 2,
      Continuous (gamma (-1) i) ∧ Function.Injective (gamma (-1) i) := by
    simpa [gamma, v, aa, sg] using hminusCont
  have hplusDis' : Disjoint (range (gamma 1 0)) (range (gamma 1 1)) := by
    simpa [gamma, v, aa, sg] using hplusDis
  have hplusClosed' : La ∩ Dc = ⋃ i : Fin 2, range (gamma 1 i) := by
    simpa [La, Dc, gamma, v, aa, sg] using hplusClosed
  have hminusClosed' : La ∩ Dc = ⋃ i : Fin 2, range (gamma (-1) i) := by
    simpa [La, Dc, gamma, v, aa, sg] using hminusClosed
  have hZcompact (i : Fin 2) : IsCompact (range (q i)) :=
    isCompact_range (hq i)
  have hZclosed (i : Fin 2) : IsClosed (range (q i)) :=
    (hZcompact i).isClosed
  have hZnonempty (i : Fin 2) : (range (q i)).Nonempty := by
    exact ⟨q i (circleDirection (0 : E2)), mem_range_self _⟩
  have hZsub (i : Fin 2) : range (q i) ⊆ La := by
    intro y hy
    rw [← hlevel']
    exact mem_iUnion.mpr ⟨i, hy⟩
  have hcomp0 : La \ range (q 0) = range (q 1) := by
    ext y
    constructor
    · rintro ⟨hy, hnot⟩
      rw [← hlevel'] at hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      fin_cases i
      · exact False.elim (hnot hi)
      · exact hi
    · intro hy
      refine ⟨hZsub 1 hy, ?_⟩
      intro hi
      exact disjoint_left.mp hqd hi hy
  have hcomp1 : La \ range (q 1) = range (q 0) := by
    ext y
    constructor
    · rintro ⟨hy, hnot⟩
      rw [← hlevel'] at hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      fin_cases i
      · exact hi
      · exact False.elim (hnot hi)
    · intro hy
      refine ⟨hZsub 0 hy, ?_⟩
      intro hi
      exact disjoint_left.mp hqd hy hi
  have hcomp (i : Fin 2) : La \ range (q i) = range (q (other i)) := by
    fin_cases i <;> simp [other, hcomp0, hcomp1]
  have hZDc (i : Fin 2) : (range (q i) ∩ Dc).Nonempty := by
    by_contra hne
    have hdj : Disjoint (range (q i)) Dc := by
      rw [Set.disjoint_iff_inter_eq_empty]
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact hne ⟨y, hy.1, hy.2⟩
    have hempty := hNoBypass (range (q i)) (hZsub i) (hZcompact i)
      (by rw [hcomp i]; exact hZcompact (other i)) hdj
    exact (hZnonempty i).ne_empty hempty
  have hgammaSubset (sigma : ℝ) (i : Fin 2)
      (hclosed : La ∩ Dc = ⋃ l : Fin 2, range (gamma sigma l)) :
      range (gamma sigma i) ⊆ La ∩ Dc := by
    intro y hy
    rw [hclosed]
    exact mem_iUnion.mpr ⟨i, hy⟩
  have hgammaCover (sigma : ℝ) (i : Fin 2)
      (hclosed : La ∩ Dc = ⋃ l : Fin 2, range (gamma sigma l)) :
      range (gamma sigma i) ⊆ range (q 0) ∪ range (q 1) := by
    intro y hy
    have hyLa := (hgammaSubset sigma i hclosed hy).1
    rw [← hlevel'] at hyLa
    obtain ⟨l, hl⟩ := mem_iUnion.mp hyLa
    fin_cases l
    · exact Or.inl hl
    · exact Or.inr hl
  have hparentChoice (sigma : ℝ) (i : Fin 2)
      (hcont : ∀ l : Fin 2, Continuous (gamma sigma l))
      (hclosed : La ∩ Dc = ⋃ l : Fin 2, range (gamma sigma l)) :
      range (gamma sigma i) ⊆ range (q 0) ∨
        range (gamma sigma i) ⊆ range (q 1) := by
    have hpre : IsPreconnected (range (gamma sigma i)) := by
      simpa only [image_univ] using
        (isPreconnected_univ.image (gamma sigma i) (hcont i).continuousOn)
    have hdisjointOn : range (gamma sigma i) ∩
        (range (q 0) ∩ range (q 1)) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact disjoint_left.mp hqd hy.2.1 hy.2.2
    apply (isPreconnected_iff_subset_of_disjoint_closed.mp hpre)
      (range (q 0)) (range (q 1)) (hZclosed 0) (hZclosed 1)
      (hgammaCover sigma i hclosed) hdisjointOn
  have hplusChoice (i : Fin 2) :
      range (gamma 1 i) ⊆ range (q 0) ∨
        range (gamma 1 i) ⊆ range (q 1) :=
    hparentChoice 1 i (fun l => (hplusCont' l).1) hplusClosed'
  have hplusParents :
      (range (gamma 1 0) ⊆ range (q 0) ∧
        range (gamma 1 1) ⊆ range (q 1)) ∨
      (range (gamma 1 0) ⊆ range (q 1) ∧
        range (gamma 1 1) ⊆ range (q 0)) := by
    rcases hplusChoice 0 with h0 | h0 <;> rcases hplusChoice 1 with h1 | h1
    · exfalso
      obtain ⟨y, hy, hdy⟩ := hZDc 1
      have hyU : y ∈ ⋃ l : Fin 2, range (gamma 1 l) := by
        rw [← hplusClosed']
        exact ⟨hZsub 1 hy, hdy⟩
      obtain ⟨l, hl⟩ := mem_iUnion.mp hyU
      fin_cases l
      · exact disjoint_left.mp hqd (h0 hl) hy
      · exact disjoint_left.mp hqd (h1 hl) hy
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr ⟨h0, h1⟩
    · exfalso
      obtain ⟨y, hy, hdy⟩ := hZDc 0
      have hyU : y ∈ ⋃ l : Fin 2, range (gamma 1 l) := by
        rw [← hplusClosed']
        exact ⟨hZsub 0 hy, hdy⟩
      obtain ⟨l, hl⟩ := mem_iUnion.mp hyU
      fin_cases l
      · exact disjoint_left.mp hqd hy (h0 hl)
      · exact disjoint_left.mp hqd hy (h1 hl)
  let tmid : unitInterval := ⟨(1 / 2 : ℝ), by norm_num⟩
  have hmidPlus : gamma 1 0 tmid =
      e.symm (Real.sqrt delta, 0) := by
    norm_num [tmid, gamma, v, aa, sg]
  have hmidMinus : gamma 1 1 tmid =
      e.symm (-Real.sqrt delta, 0) := by
    norm_num [tmid, gamma, v, aa, sg]
  have hparentPlus :
      (e.symm (Real.sqrt delta, 0) ∈ range (q 0) ∧
        range (gamma 1 0) ⊆ range (q 0) ∧
        range (gamma 1 1) ⊆ range (q 1)) ∨
      (e.symm (Real.sqrt delta, 0) ∉ range (q 0) ∧
        range (gamma 1 0) ⊆ range (q 1) ∧
        range (gamma 1 1) ⊆ range (q 0)) := by
    rcases hplusParents with h | h
    · left
      refine ⟨?_, h.1, h.2⟩
      exact h.1 ⟨tmid, hmidPlus⟩
    · right
      refine ⟨?_, h.1, h.2⟩
      intro hp
      exact disjoint_left.mp hqd hp (h.1 ⟨tmid, hmidPlus⟩)
  let iPos : Fin 2 := if e.symm (Real.sqrt delta, 0) ∈ range (q 0) then 0 else 1
  have hiPos0 : iPos = 0 ↔ e.symm (Real.sqrt delta, 0) ∈ range (q 0) := by
    simp [iPos]
  have hiPos1 : iPos = 1 ↔ e.symm (-Real.sqrt delta, 0) ∈ range (q 0) := by
    rcases hparentPlus with h | h
    · have hp : e.symm (Real.sqrt delta, 0) ∈ range (q 0) := h.1
      have hm : e.symm (-Real.sqrt delta, 0) ∉ range (q 0) := by
        intro hm
        exact disjoint_left.mp hqd hm (h.2.2 ⟨tmid, hmidMinus⟩)
      simp [iPos, hp, hm]
    · have hp : e.symm (Real.sqrt delta, 0) ∉ range (q 0) := h.1
      have hm : e.symm (-Real.sqrt delta, 0) ∈ range (q 0) :=
        h.2.2 ⟨tmid, hmidMinus⟩
      simp [iPos, hp, hm]
  have hplus0 : range (q 0) ∩ Dc = range (gamma 1 iPos) := by
    by_cases hp : e.symm (Real.sqrt delta, 0) ∈ range (q 0)
    · have h0 := hparentPlus.resolve_right (by
        intro hbad
        exact hbad.1 hp)
      have hi : iPos = 0 := by simp [iPos, hp]
      rw [hi]
      ext y
      constructor
      · rintro ⟨hy, hd⟩
        have hyU : y ∈ ⋃ l : Fin 2, range (gamma 1 l) := by
          rw [← hplusClosed']
          exact ⟨hZsub 0 hy, hd⟩
        obtain ⟨l, hl⟩ := mem_iUnion.mp hyU
        fin_cases l
        · exact hl
        · exact False.elim (disjoint_left.mp hqd hy (h0.2.2 hl))
      · intro hy
        exact ⟨h0.2.1 hy, (hgammaSubset 1 0 hplusClosed' hy).2⟩
    · have h1 := hparentPlus.resolve_left (by
        intro hgood
        exact hp hgood.1)
      have hi : iPos = 1 := by simp [iPos, hp]
      rw [hi]
      ext y
      constructor
      · rintro ⟨hy, hd⟩
        have hyU : y ∈ ⋃ l : Fin 2, range (gamma 1 l) := by
          rw [← hplusClosed']
          exact ⟨hZsub 0 hy, hd⟩
        obtain ⟨l, hl⟩ := mem_iUnion.mp hyU
        fin_cases l
        · exact False.elim (disjoint_left.mp hqd hy (h1.2.1 hl))
        · exact hl
      · intro hy
        exact ⟨h1.2.2 hy, (hgammaSubset 1 1 hplusClosed' hy).2⟩
  have hplus1 : range (q 1) ∩ Dc = range (gamma 1 (other iPos)) := by
    by_cases hp : e.symm (Real.sqrt delta, 0) ∈ range (q 0)
    · have h := hparentPlus.resolve_right (by
        intro hbad
        exact hbad.1 hp)
      have hi : other iPos = 1 := by simp [iPos, hp, other]
      rw [hi]
      ext y
      constructor
      · rintro ⟨hy, hd⟩
        have hyU : y ∈ ⋃ l : Fin 2, range (gamma 1 l) := by
          rw [← hplusClosed']
          exact ⟨hZsub 1 hy, hd⟩
        obtain ⟨l, hl⟩ := mem_iUnion.mp hyU
        fin_cases l
        · exact False.elim (disjoint_left.mp hqd (h.2.1 hl) hy)
        · exact hl
      · intro hy
        exact ⟨h.2.2 hy, (hgammaSubset 1 1 hplusClosed' hy).2⟩
    · have h := hparentPlus.resolve_left (by
        intro hgood
        exact hp hgood.1)
      have hi : other iPos = 0 := by simp [iPos, hp, other]
      rw [hi]
      ext y
      constructor
      · rintro ⟨hy, hd⟩
        have hyU : y ∈ ⋃ l : Fin 2, range (gamma 1 l) := by
          rw [← hplusClosed']
          exact ⟨hZsub 1 hy, hd⟩
        obtain ⟨l, hl⟩ := mem_iUnion.mp hyU
        fin_cases l
        · exact hl
        · exact False.elim (disjoint_left.mp hqd (h.2.2 hl) hy)
      · intro hy
        exact ⟨h.2.1 hy, (hgammaSubset 1 0 hplusClosed' hy).2⟩
  have hplus0Sub : range (gamma 1 iPos) ⊆ range (q 0) := by
    intro y hy
    have hmem : y ∈ range (q 0) ∩ Dc := by
      rw [hplus0]
      exact hy
    exact hmem.1
  have hflip (i : Fin 2) : range (gamma (-1) i) = range (gamma 1 (other i)) := by
    ext y
    constructor <;> rintro ⟨t, rfl⟩
    · exact ⟨t, by fin_cases i <;> simp [gamma, v, aa, sg, other]⟩
    · exact ⟨t, by fin_cases i <;> simp [gamma, v, aa, sg, other]⟩
  have hother (i : Fin 2) : other (other i) = i := by
    fin_cases i <;> rfl
  have hminus0 : range (q 0) ∩ Dc = range (gamma (-1) (other iPos)) := by
    rw [hflip]
    rw [hother]
    exact hplus0
  have hminus1 : range (q 1) ∩ Dc = range (gamma (-1) iPos) := by
    rw [hflip]
    exact hplus1
  let iRef : ℝ → Fin 2 := fun sigma => if sigma = 1 then iPos else other iPos
  have hiRefFlip : iRef (-1) = other (iRef 1) := by
    have hneg : (-1 : ℝ) ≠ 1 := by norm_num
    simp only [iRef, if_neg hneg, if_pos rfl]
  have hotherOfNe (a b : Fin 2) (hab : a ≠ b) : other a = b := by
    fin_cases a <;> fin_cases b
    · exact (hab rfl).elim
    · rfl
    · rfl
    · exact (hab rfl).elim
  have hminusSelected : range (gamma (-1) (other iPos)) ⊆ range (q 0) := by
    intro y hy
    have hy' : y ∈ range (gamma 1 (other (other iPos))) := by
      rw [← hflip (other iPos)]
      exact hy
    rw [hother] at hy'
    exact hplus0Sub hy'
  have hInter : ∀ sigma : ℝ, sigma = 1 ∨ sigma = -1 →
      range (q 0) ∩ Dc = range (gamma sigma (iRef sigma)) ∧
      range (q 1) ∩ Dc = range (gamma sigma (other (iRef sigma))) := by
    intro sigma hs
    rcases hs with rfl | rfl
    · constructor
      · simpa only [iRef, if_pos rfl] using hplus0
      · simpa only [iRef, if_pos rfl] using hplus1
    · constructor
      · have hneg : (-1 : ℝ) ≠ 1 := by norm_num
        simpa only [iRef, if_neg hneg] using hminus0
      · have hneg : (-1 : ℝ) ≠ 1 := by norm_num
        have hi : other (iRef (-1)) = iPos := by
          simp only [iRef, if_neg hneg]
          exact hother iPos
        rw [hi]
        exact hminus1
  refine ⟨iPos, hiPos0, hiPos1, ?_⟩
  change iRef (-1) = other (iRef 1) ∧
    (∀ sigma : ℝ, sigma = 1 ∨ sigma = -1 →
      range (q 0) ∩ Dc = range (gamma sigma (iRef sigma)) ∧
      range (q 1) ∩ Dc = range (gamma sigma (other (iRef sigma)))) ∧
    ∀ iTar : Fin 2,
      let sigma : ℝ := if iPos = iTar then 1 else -1
      (sigma = 1 ∨ sigma = -1) ∧ iRef sigma = iTar ∧
      ∀ label : Fin 2 ≃ Fin 2,
        (∀ i : Fin 2, range (gamma sigma i) ⊆ range (q (label i))) →
        label.symm 0 = iTar
  refine ⟨hiRefFlip, hInter, ?_⟩
  intro iTar
  let sigma : ℝ := if iPos = iTar then 1 else -1
  have hsigma : sigma = 1 ∨ sigma = -1 := by
    by_cases h : iPos = iTar <;> simp [sigma, h]
  have hi : (if sigma = 1 then iPos else other iPos) = iTar := by
    by_cases h : iPos = iTar
    · have hs : sigma = 1 := by simp [sigma, h]
      rw [hs, if_pos rfl]
      exact h
    · have ho : other iPos = iTar := hotherOfNe iPos iTar h
      have hs : sigma = -1 := by simp [sigma, h]
      rw [hs]
      have hneg : (-1 : ℝ) ≠ 1 := by norm_num
      simpa only [if_neg hneg] using ho
  refine ⟨hsigma, hi, ?_⟩
  intro label hlabel
  have hselected : range (gamma sigma ((if sigma = 1 then iPos else other iPos))) ⊆
      range (q 0) := by
    by_cases h : iPos = iTar
    · have hs : sigma = 1 := by simp [sigma, h]
      rw [hs, if_pos rfl]
      exact hplus0Sub
    · have hs : sigma = -1 := by simp [sigma, h]
      rw [hs]
      have hneg : (-1 : ℝ) ≠ 1 := by norm_num
      simpa only [if_neg hneg] using hminusSelected
  have hfin2 (x : Fin 2) (hx : x ≠ 0) : x = 1 := by
    fin_cases x
    · exact (hx rfl).elim
    · rfl
  have hlabelZero : label (if sigma = 1 then iPos else other iPos) = 0 := by
    by_contra hne
    have hEqOne : label (if sigma = 1 then iPos else other iPos) = 1 :=
      hfin2 _ hne
    let t0 : unitInterval := ⟨0, by norm_num⟩
    have hq0 : gamma sigma (if sigma = 1 then iPos else other iPos) t0 ∈
        range (q 0) := hselected ⟨t0, rfl⟩
    have hq1 : gamma sigma (if sigma = 1 then iPos else other iPos) t0 ∈
        range (q (label (if sigma = 1 then iPos else other iPos))) :=
      hlabel _ ⟨t0, rfl⟩
    rw [hEqOne] at hq1
    exact disjoint_left.mp hqd hq0 hq1
  apply label.injective
  calc
    label (label.symm 0) = 0 := label.apply_symm_apply 0
    _ = label (if sigma = 1 then iPos else other iPos) := hlabelZero.symm
    _ = label iTar := congrArg label hi

end PoincareConjecture.M25.Topology3D
