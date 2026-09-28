import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SourceCircleCut
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.SelectedOrientedExteriorArcs
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CircleRadialChart











set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D




theorem exists_saddle_native_source_exterior_arcs
    (q : Fin 2 → UnitCircle → UnitTwoSphere)
    (hq : ∀ i : Fin 2,
      ContMDiff (𝓡 1) (𝓡 2) ∞ (q i) ∧ Function.Injective (q i) ∧
      ∀ theta : UnitCircle,
        Function.Injective (mfderiv (𝓡 1) (𝓡 2) (q i) theta))
    (hqd : ∀ i l : Fin 2, i ≠ l →
      Disjoint (range (q i)) (range (q l)))
    (gamma : Fin 2 → unitInterval → UnitTwoSphere)
    (hgamma : ∀ i : Fin 2, Continuous (gamma i) ∧ Function.Injective (gamma i))
    (hgdisjoint : Disjoint (range (gamma 0)) (range (gamma 1)))
    (p : Fin 4 → UnitTwoSphere)
    (hend : ∀ i : Fin 2,
      gamma i 0 = p (finProdFinEquiv (i, (0 : Fin 2))) ∧
      gamma i 1 = p (finProdFinEquiv (i, (1 : Fin 2))))
    (La V Dc : Set UnitTwoSphere)
    (hlevel : (⋃ i : Fin 2, range (q i)) = La)
    (hclosed : La ∩ Dc = ⋃ i : Fin 2, range (gamma i))
    (hopen : La ∩ V = ⋃ i : Fin 2, gamma i '' Ioo (0 : unitInterval) 1)
    (hNoBypass : ∀ B : Set UnitTwoSphere, B ⊆ La → IsCompact B →
      IsCompact (La \ B) → Disjoint B Dc → B = ∅) :
    ∃ (label : Fin 2 ≃ Fin 2) (a v : Fin 2 → ℝ) (eta : ℝ),
    let alpha : Fin 2 → ℝ → UnitTwoSphere := fun i t =>
      q (label i) (complexUnitCircleHomeomorph (Circle.exp (a i + v i * t)))
    (∀ i : Fin 2, IsCompact (range (q i)) ∧ IsCompact (La \ range (q i))) ∧
    Function.Injective p ∧ 0 < eta ∧ eta < 1 / 8 ∧
    (∀ i : Fin 2, range (gamma i) ⊆ range (q (label i))) ∧
    (∀ i : Fin 2,
      0 < |v i| ∧ |v i| < 2 * Real.pi ∧
      ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (alpha i) ∧
      (∀ t : ℝ, Function.Injective
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (alpha i) t)) ∧
      Set.InjOn (alpha i) (Icc (-eta) (1 + eta)) ∧
      alpha i 0 = p (finProdFinEquiv (i, (0 : Fin 2))) ∧
      alpha i 1 = p (finProdFinEquiv (i, (1 : Fin 2))) ∧
      Disjoint (alpha i '' Ioo (0 : ℝ) 1) Dc ∧
      (alpha i '' Icc (0 : ℝ) 1) ∩ Dc =
        {p (finProdFinEquiv (i, (0 : Fin 2))),
          p (finProdFinEquiv (i, (1 : Fin 2)))} ∧
      (∀ s ∈ Ioo (-eta) (0 : ℝ), alpha i s ∈ V) ∧
      (∀ s ∈ Ioo (1 : ℝ) (1 + eta), alpha i s ∈ V)) ∧
    Disjoint (alpha 0 '' Icc (-eta) (1 + eta))
      (alpha 1 '' Icc (-eta) (1 + eta)) ∧
    La \ V = ⋃ i : Fin 2, alpha i '' Icc (0 : ℝ) 1 ∧
    La ∩ (Dc \ V) = range p ∧
    ∀ i : Fin 2,
      range (q (label i)) ∩ Dc = range (gamma i) ∧
      range (q (label i)) ∩ V = gamma i '' Ioo (0 : unitInterval) 1 ∧
      range (q (label i)) \ V = alpha i '' Icc (0 : ℝ) 1 ∧
      range (q (label i)) =
        (alpha i '' Icc (0 : ℝ) 1) ∪ range (gamma i) := by
  classical
  have hqLa (i : Fin 2) : range (q i) ⊆ La := by
    intro y hy
    rw [← hlevel]
    exact mem_iUnion.mpr ⟨i, hy⟩
  have hqCompact (i : Fin 2) : IsCompact (range (q i)) :=
    isCompact_range (hq i).1.continuous
  have hcomplement (i : Fin 2) :
      La \ range (q i) = ⋃ l : {l : Fin 2 // l ≠ i}, range (q l.1) := by
    ext y
    constructor
    · rintro ⟨hy, hnot⟩
      rw [← hlevel] at hy
      obtain ⟨l, hl⟩ := mem_iUnion.mp hy
      have hli : l ≠ i := by
        intro heq
        subst l
        exact hnot hl
      exact mem_iUnion.mpr ⟨⟨l, hli⟩, hl⟩
    · intro hy
      obtain ⟨l, hl⟩ := mem_iUnion.mp hy
      exact ⟨hqLa l.1 hl, fun hi => disjoint_left.mp (hqd l.1 i l.2) hl hi⟩
  have hcomplementCompact (i : Fin 2) : IsCompact (La \ range (q i)) := by
    rw [hcomplement i]
    exact isCompact_iUnion (fun l => hqCompact l.1)
  have hnoBypass (i : Fin 2) : ¬ Disjoint (range (q i)) Dc := by
    intro hi
    have hempty := hNoBypass (range (q i)) (hqLa i) (hqCompact i)
      (hcomplementCompact i) hi
    have hnonempty : (range (q i)).Nonempty :=
      ⟨q i (circleDirection (0 : E2)), circleDirection (0 : E2), rfl⟩
    exact hnonempty.ne_empty hempty
  obtain ⟨removedParent, arcParent, aOld, vOld, ends, eta,
      hp, heta, hetaSmall, hparent, harcs, hArcDisjoint,
      _hArcBypass, hBypassIff, hcover, hrim, hcard, hdifferent, _hsame⟩ :=
    exists_saddle_source_circle_cut 2 q hq hqd
      gamma hgamma hgdisjoint p hend V Dc
      (by rw [hlevel]; exact hclosed)
      (by rw [hlevel]; exact hopen)
  let bypass : Finset (Fin 2) := Finset.univ \ {removedParent 0, removedParent 1}
  change (∀ i : Fin 2, i ∈ bypass ↔ Disjoint (range (q i)) Dc) at hBypassIff
  have hbempty : bypass = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    exact hnoBypass i ((hBypassIff i).mp hi)
  change bypass.card + (if removedParent 0 = removedParent 1 then 1 else 2) = 2 at hcard
  have hdistinct : removedParent 0 ≠ removedParent 1 := by
    intro heq
    norm_num [hbempty, heq] at hcard
  have hremoved : Injective removedParent := by
    intro i l hil
    fin_cases i <;> fin_cases l
    · rfl
    · exact False.elim (hdistinct hil)
    · exact False.elim (hdistinct hil.symm)
    · rfl
  let label : Fin 2 ≃ Fin 2 := Equiv.ofBijective removedParent
    ⟨hremoved, Finite.surjective_of_injective hremoved⟩
  obtain ⟨hArcParent, hpairs⟩ := hdifferent hdistinct
  subst arcParent
  let alphaOld : Fin 2 → ℝ → UnitTwoSphere := fun i t =>
    q (label i) (complexUnitCircleHomeomorph (Circle.exp (aOld i + vOld i * t)))
  have hbunion : (⋃ i ∈ bypass, range (q i)) = (∅ : Set UnitTwoSphere) := by
    rw [hbempty]
    simp
  have hcoverOld : La \ V = (⋃ i : Fin 2, alphaOld i '' Icc (0 : ℝ) 1) ∪
      (⋃ i ∈ bypass, range (q i)) := by
    rw [← hlevel]
    exact hcover
  rw [hbunion, union_empty] at hcoverOld
  have hrim' : La ∩ (Dc \ V) = range p := by
    rw [← hlevel]
    exact hrim
  obtain ⟨a, v, _ha, _hv, _hReflection, _hImages,
      hOrdered, hOrderedDisjoint, hOrderedCover⟩ :=
    exists_saddle_selected_oriented_exterior_arcs q label aOld vOld ends eta p Dc V La
      harcs hArcDisjoint hcoverOld hpairs
  let alpha : Fin 2 → ℝ → UnitTwoSphere := fun i t =>
    q (label i) (complexUnitCircleHomeomorph (Circle.exp (a i + v i * t)))
  have hcoverFinal : La \ V = ⋃ i : Fin 2, alpha i '' Icc (0 : ℝ) 1 := hOrderedCover
  have hParent (i : Fin 2) : range (gamma i) ⊆ range (q (label i)) := hparent i
  have hlabel (i l : Fin 2) {y : UnitTwoSphere}
      (hi : y ∈ range (q (label i))) (hl : y ∈ range (q (label l))) : i = l := by
    apply label.injective
    by_contra hne
    exact disjoint_left.mp (hqd (label i) (label l) hne) hi hl
  have hGamma (i : Fin 2) {y : UnitTwoSphere} (hy : y ∈ range (gamma i)) :
      y ∈ La ∩ Dc := by
    rw [hclosed]
    exact mem_iUnion.mpr ⟨i, hy⟩
  have hGammaOpen (i : Fin 2) {y : UnitTwoSphere}
      (hy : y ∈ gamma i '' Ioo (0 : unitInterval) 1) : y ∈ La ∩ V := by
    rw [hopen]
    exact mem_iUnion.mpr ⟨i, hy⟩
  have hAlpha (i : Fin 2) {y : UnitTwoSphere}
      (hy : y ∈ alpha i '' Icc (0 : ℝ) 1) : y ∈ La \ V := by
    rw [hcoverFinal]
    exact mem_iUnion.mpr ⟨i, hy⟩
  have hAlphaParent (i : Fin 2) {y : UnitTwoSphere}
      (hy : y ∈ alpha i '' Icc (0 : ℝ) 1) : y ∈ range (q (label i)) := by
    rcases hy with ⟨t, _, rfl⟩
    exact mem_range_self _
  have hClosedEach (i : Fin 2) : range (q (label i)) ∩ Dc = range (gamma i) := by
    ext y
    constructor
    · rintro ⟨hy, hd⟩
      have hm : y ∈ ⋃ l : Fin 2, range (gamma l) := by
        rw [← hclosed]
        exact ⟨hqLa (label i) hy, hd⟩
      obtain ⟨l, hl⟩ := mem_iUnion.mp hm
      have hil := hlabel i l hy (hParent l hl)
      subst l
      exact hl
    · intro hy
      exact ⟨hParent i hy, (hGamma i hy).2⟩
  have hOpenEach (i : Fin 2) :
      range (q (label i)) ∩ V = gamma i '' Ioo (0 : unitInterval) 1 := by
    ext y
    constructor
    · rintro ⟨hy, hv⟩
      have hm : y ∈ ⋃ l : Fin 2, gamma l '' Ioo (0 : unitInterval) 1 := by
        rw [← hopen]
        exact ⟨hqLa (label i) hy, hv⟩
      obtain ⟨l, hl⟩ := mem_iUnion.mp hm
      have hly : y ∈ range (gamma l) := by
        obtain ⟨t, _, ht⟩ := hl
        exact ⟨t, ht⟩
      have hil := hlabel i l hy (hParent l hly)
      subst l
      exact hl
    · intro hy
      have hiy : y ∈ range (gamma i) := by
        obtain ⟨t, _, ht⟩ := hy
        exact ⟨t, ht⟩
      exact ⟨hParent i hiy, (hGammaOpen i hy).2⟩
  have hExteriorEach (i : Fin 2) :
      range (q (label i)) \ V = alpha i '' Icc (0 : ℝ) 1 := by
    ext y
    constructor
    · rintro ⟨hy, hv⟩
      have hm : y ∈ ⋃ l : Fin 2, alpha l '' Icc (0 : ℝ) 1 := by
        rw [← hcoverFinal]
        exact ⟨hqLa (label i) hy, hv⟩
      obtain ⟨l, hl⟩ := mem_iUnion.mp hm
      have hil := hlabel i l hy (hAlphaParent l hl)
      subst l
      exact hl
    · intro hy
      exact ⟨hAlphaParent i hy, (hAlpha i hy).2⟩
  have hFullEach (i : Fin 2) : range (q (label i)) =
      (alpha i '' Icc (0 : ℝ) 1) ∪ range (gamma i) := by
    ext y
    constructor
    · intro hy
      by_cases hv : y ∈ V
      · have hmem : y ∈ gamma i '' Ioo (0 : unitInterval) 1 := by
          have hpair : y ∈ range (q (label i)) ∩ V := ⟨hy, hv⟩
          rw [hOpenEach i] at hpair
          exact hpair
        obtain ⟨t, _, ht⟩ := hmem
        exact Or.inr ⟨t, ht⟩
      · have hmem : y ∈ alpha i '' Icc (0 : ℝ) 1 := by
          have hpair : y ∈ range (q (label i)) \ V := ⟨hy, hv⟩
          rw [hExteriorEach i] at hpair
          exact hpair
        exact Or.inl hmem
    · rintro (hy | hy)
      · have hmem : y ∈ range (q (label i)) \ V := by
          rw [hExteriorEach i]
          exact hy
        exact hmem.1
      · exact hParent i hy
  exact ⟨label, a, v, eta, (fun i => ⟨hqCompact i, hcomplementCompact i⟩),
    hp, heta, hetaSmall, hParent, hOrdered, hOrderedDisjoint, hcoverFinal, hrim',
    fun i => ⟨hClosedEach i, hOpenEach i, hExteriorEach i, hFullEach i⟩⟩

end PoincareConjecture.M25.Topology3D
