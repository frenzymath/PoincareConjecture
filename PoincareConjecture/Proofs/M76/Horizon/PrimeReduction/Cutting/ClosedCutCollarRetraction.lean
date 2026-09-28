import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.CollarEndRetraction









set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem exists_collarCoverOuter_contraction
    {X κ : Type*} [TopologicalSpace X] [Finite κ]
    {A : κ → Type*} [∀ i, TopologicalSpace (A i)]
    (R Q : Set X) (O : κ → Set X)
    (W : ∀ i, (A i × unitInterval) ≃ₜ closure (O i))
    (hQ : Q = R \ ⋃ i, O i) (hcQ : IsClosed Q)
    (hCR : ∀ i, closure (O i) ⊆ R)
    (hdis : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hO : ∀ i z, (W i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1) :
    ∃ F : C(unitInterval × collarCoverOuter R W, collarCoverOuter R W),
      (∀ x, F (0, x) = x) ∧
      (∀ x, ((F (1, x)).val : X) ∈ Q) ∧
      (∀ s x, (x.val : X) ∈ Q → F (s, x) = x) := by
  classical
  let U := collarCoverOuter R W
  let P : Option κ → Set (unitInterval × U) := fun j => match j with
    | none => {z | (z.2.val : X) ∈ Q}
    | some i => {z | (z.2.val : X) ∈ closure (O i)}
  let coord (i : κ) (z : P (some i)) : A i × unitInterval :=
    (W i).symm ⟨z.val.2.val, z.property⟩
  have hc (i : κ) : Continuous (coord i) :=
    (W i).symm.continuous.comp
      ((continuous_subtype_val.comp (continuous_subtype_val.comp
        (continuous_snd.comp continuous_subtype_val))).subtype_mk _)
  have ht (i : κ) (z : P (some i)) :
      ((coord i z).2 : ℝ) < 1 / 4 ∨ (3 / 4 : ℝ) < (coord i z).2 := by
    apply (collarCoverOuter_coordinates R W hCR hdis i (coord i z)).mp
    simpa only [coord, Homeomorph.apply_symm_apply] using z.val.2.property
  let tm (i : κ) (z : P (some i)) : CollarEnds := ⟨(coord i z).2, ht i z⟩
  have htm (i : κ) : Continuous (tm i) := ((hc i).snd).subtype_mk _
  let H : ∀ j, C(P j, X) := fun j => match j with
    | none => ⟨fun z => z.val.2.val,
        continuous_subtype_val.comp (continuous_subtype_val.comp
          (continuous_snd.comp continuous_subtype_val))⟩
    | some i => ⟨fun z => W i ((coord i z).1, collarEndSlide z.val.1 (tm i z)),
        continuous_subtype_val.comp ((W i).continuous.comp
          ((hc i).fst.prodMk (continuous_collarEndSlide.comp
            ((continuous_fst.comp continuous_subtype_val).prodMk (htm i)))))⟩
  have hnot (i : κ) (x : closure (O i)) :
      (x : X) ∈ Q ↔ (x : X) ∉ O i := by
    rw [hQ]
    simp only [mem_sdiff, hCR i x.property, true_and]
    constructor
    · exact fun hx hi => hx (mem_iUnion.mpr ⟨i, hi⟩)
    · intro hx hf
      obtain ⟨j, hj⟩ := mem_iUnion.mp hf
      by_cases he : i = j
      · exact hx (he ▸ hj)
      · exact disjoint_left.mp (hdis he) x.property (subset_closure hj)
  have hfix (i : κ) (z : P (some i)) (hz : (z.val.2.val : X) ∈ Q) :
      H (some i) z = z.val.2.val := by
    have hn : ¬ ((0 : ℝ) < (coord i z).2 ∧ ((coord i z).2 : ℝ) < 1) := by
      rw [← hO i]
      simpa only [coord, Homeomorph.apply_symm_apply] using
        (hnot i ⟨z.val.2.val, z.property⟩).mp hz
    have he : (coord i z).2 = 0 ∨ (coord i z).2 = 1 := by
      by_cases hh : ((coord i z).2 : ℝ) = 0
      · exact Or.inl (Subtype.ext hh)
      · right
        apply Subtype.ext
        have := (coord i z).2.property
        have hp : (0 : ℝ) < (coord i z).2 := lt_of_le_of_ne this.1 (Ne.symm hh)
        have := not_lt.mp (fun hh => hn ⟨hp, hh⟩)
        exact le_antisymm (coord i z).2.property.2 this
    change (W i ((coord i z).1, collarEndSlide z.val.1 (tm i z)) : X) = _
    rw [collarEndSlide_fixed _ _ he]
    exact congrArg Subtype.val ((W i).apply_symm_apply _)
  have hagree : ∀ j k z (hj : z ∈ P j) (hk : z ∈ P k),
      H j ⟨z, hj⟩ = H k ⟨z, hk⟩ := by
    intro j k z hj hk
    cases j with
    | none =>
      cases k with
      | none => rfl
      | some i => exact (hfix i ⟨z, hk⟩ hj).symm
    | some i =>
      cases k with
      | none => exact hfix i ⟨z, hj⟩ hk
      | some j =>
        by_cases he : i = j
        · subst j; rfl
        · exact False.elim (disjoint_left.mp (hdis he) hj hk)
  have hcover : ⋃ j, P j = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro z
    by_cases hz : (z.2.val : X) ∈ Q
    · exact ⟨none, hz⟩
    · have hx : (z.2.val : X) ∈ ⋃ i, O i := by
        by_contra hn
        exact hz (hQ ▸ ⟨z.2.val.property, hn⟩)
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact ⟨some i, subset_closure hi⟩
  let G := Set.liftCover P (fun j => H j) hagree hcover
  have hval (j : Option κ) (z : P j) : G z = H j z := Set.liftCover_coe z
  have hG : Continuous G := by
    apply (locallyFinite_of_finite P).continuous hcover
    · intro j
      cases j with
      | none => exact hcQ.preimage (continuous_subtype_val.comp
          (continuous_subtype_val.comp continuous_snd))
      | some i => exact isClosed_closure.preimage (continuous_subtype_val.comp
          (continuous_subtype_val.comp continuous_snd))
    · intro j
      rw [continuousOn_iff_continuous_domRestrict]
      have he : (P j).domRestrict G = H j := funext (hval j)
      rw [he]
      exact (H j).continuous
  have hGR (z : unitInterval × U) : G z ∈ R := by
    obtain ⟨j, hj⟩ := iUnion_eq_univ_iff.mp hcover z
    rw [hval j ⟨z, hj⟩]
    cases j with
    | none => exact z.2.val.property
    | some i => exact hCR i (W i _).property
  have hGU (z : unitInterval × U) : (⟨G z, hGR z⟩ : R) ∈ U := by
    change G z ∉ ⋃ i, collarMiddle (W i)
    obtain ⟨j, hj⟩ := iUnion_eq_univ_iff.mp hcover z
    rw [hval j ⟨z, hj⟩]
    cases j with
    | none => exact z.2.property
    | some i =>
      exact (collarCoverOuter_coordinates R W hCR hdis i _).mpr
        (collarEndSlide_mem z.1 (tm i ⟨z, hj⟩))
  let F : C(unitInterval × U, U) :=
    ⟨fun z => ⟨⟨G z, hGR z⟩, hGU z⟩, (hG.subtype_mk _).subtype_mk _⟩
  refine ⟨F, ?_, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨j, hj⟩ := iUnion_eq_univ_iff.mp hcover (0, x)
    change G (0, x) = (x.val : X)
    rw [hval j ⟨(0, x), hj⟩]
    cases j with
    | none => rfl
    | some i =>
      change (W i ((coord i ⟨(0, x), hj⟩).1,
        collarEndSlide 0 (tm i ⟨(0, x), hj⟩)) : X) = _
      rw [collarEndSlide_zero]
      exact congrArg Subtype.val ((W i).apply_symm_apply _)
  · intro x
    obtain ⟨j, hj⟩ := iUnion_eq_univ_iff.mp hcover (1, x)
    change G (1, x) ∈ Q
    rw [hval j ⟨(1, x), hj⟩]
    cases j with
    | none => exact hj
    | some i =>
      apply (hnot i (W i _)).mpr
      rw [hO i]
      change ¬ ((0 : ℝ) < collarEndSlide 1 (tm i ⟨(1, x), hj⟩) ∧
        (collarEndSlide 1 (tm i ⟨(1, x), hj⟩) : ℝ) < 1)
      rw [collarEndSlide_one]
      unfold collarEnd
      split_ifs <;> norm_num
  · intro s x hx
    apply Subtype.ext
    apply Subtype.ext
    exact hval none ⟨(s, x), hx⟩

end PoincareConjecture.M76
