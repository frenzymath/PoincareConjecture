import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.ClosedCutCollarRetraction

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

def PuncturedCollarInterval := {t : unitInterval | (t : ℝ) ≠ 1 / 2}

noncomputable def puncturedCollarEnd (t : PuncturedCollarInterval) : unitInterval :=
  if (t.val : ℝ) < 1 / 2 then 0 else 1

theorem continuous_puncturedCollarEnd : Continuous puncturedCollarEnd := by
  have hc : Continuous (fun t : PuncturedCollarInterval => (t.val : ℝ)) :=
    continuous_subtype_val.comp continuous_subtype_val
  have he : {t : PuncturedCollarInterval | (t.val : ℝ) < 1 / 2}ᶜ =
      {t | (1 / 2 : ℝ) < t.val} := by
    ext t
    simp only [mem_compl_iff,mem_ofPred_eq,not_lt]
    exact le_iff_lt_or_eq.trans (or_iff_left (Ne.symm t.property))
  have hcl : IsClopen {t : PuncturedCollarInterval | (t.val : ℝ) < 1 / 2} :=
    ⟨isOpen_compl_iff.mp (he ▸ isOpen_lt continuous_const hc),
      isOpen_lt hc continuous_const⟩
  apply Continuous.if _ continuous_const continuous_const
  intro t ht
  rw [hcl.frontier_eq] at ht
  exact False.elim ht

noncomputable def puncturedCollarSlide
    (s : unitInterval) (t : PuncturedCollarInterval) : unitInterval :=
  ⟨(1 - (s : ℝ)) * t.val + (s : ℝ) * puncturedCollarEnd t, by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr s.property.2) t.val.property.1)
        (mul_nonneg s.property.1 (puncturedCollarEnd t).property.1)
    · have h0 := t.val.property.2
      have h1 := (puncturedCollarEnd t).property.2
      nlinarith [s.property.1,s.property.2]⟩

theorem continuous_puncturedCollarSlide :
    Continuous (fun z : unitInterval × PuncturedCollarInterval =>
      puncturedCollarSlide z.1 z.2) := by
  apply Continuous.subtype_mk
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))).add
    ((continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp (continuous_puncturedCollarEnd.comp continuous_snd)))

theorem puncturedCollarSlide_ne (s : unitInterval) (t : PuncturedCollarInterval) :
    (puncturedCollarSlide s t : ℝ) ≠ 1 / 2 := by
  rcases lt_or_gt_of_ne t.property with ht | ht
  · have he : puncturedCollarEnd t = 0 := if_pos ht
    apply ne_of_lt
    change (1 - (s : ℝ)) * t.val + (s : ℝ) * puncturedCollarEnd t < 1 / 2
    rw [he]
    change (1 - (s : ℝ)) * t.val + (s : ℝ) * 0 < 1 / 2
    nlinarith [s.property.1,t.val.property.1]
  · have he : puncturedCollarEnd t = 1 := if_neg (not_lt.mpr ht.le)
    apply ne_of_gt
    change (1 / 2 : ℝ) < (1 - (s : ℝ)) * t.val + (s : ℝ) * puncturedCollarEnd t
    rw [he]
    change (1 / 2 : ℝ) < (1 - (s : ℝ)) * t.val + (s : ℝ) * 1
    nlinarith [s.property.1,t.val.property.2]

@[simp] theorem puncturedCollarSlide_zero (t : PuncturedCollarInterval) :
    puncturedCollarSlide 0 t = t.val := by
  apply Subtype.ext
  simp [puncturedCollarSlide]

@[simp] theorem puncturedCollarSlide_one (t : PuncturedCollarInterval) :
    puncturedCollarSlide 1 t = puncturedCollarEnd t := by
  apply Subtype.ext
  simp [puncturedCollarSlide]

theorem puncturedCollarSlide_fixed (s : unitInterval) (t : PuncturedCollarInterval)
    (ht : t.val = 0 ∨ t.val = 1) : puncturedCollarSlide s t = t.val := by
  rcases ht with ht | ht
  · have he : puncturedCollarEnd t = 0 := by simp [puncturedCollarEnd,ht]
    apply Subtype.ext
    simp [puncturedCollarSlide,ht,he]
  · have he : puncturedCollarEnd t = 1 := by norm_num [puncturedCollarEnd,ht]
    apply Subtype.ext
    simp [puncturedCollarSlide,ht,he]

theorem exists_raw_sphere_cut_retraction
    {X κ : Type*} [TopologicalSpace X] [Finite κ]
    {A : κ → Type*} [∀ i, TopologicalSpace (A i)]
    (R Q : Set X) (O S : κ → Set X)
    (W : ∀ i, (A i × unitInterval) ≃ₜ closure (O i))
    (hQ : Q = R \ ⋃ i, O i) (hcQ : IsClosed Q)
    (hCR : ∀ i, closure (O i) ⊆ R)
    (hdis : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (hO : ∀ i z, (W i z : X) ∈ O i ↔ (0 : ℝ) < z.2 ∧ (z.2 : ℝ) < 1)
    (hS : ∀ i z, (W i z : X) ∈ S i ↔ (z.2 : ℝ) = 1 / 2)
    (hSC : ∀ i, S i ⊆ closure (O i)) :
    ∃ F : C(unitInterval × (R \ ⋃ i, S i : Set X), (R \ ⋃ i, S i : Set X)),
      (∀ x, F (0,x) = x) ∧
      (∀ x, (F (1,x) : X) ∈ Q) ∧
      (∀ s (x : (R \ ⋃ i, S i : Set X)), (x : X) ∈ Q → F (s,x) = x) := by
  classical
  let U := R \ ⋃ i, S i
  let P : Option κ → Set (unitInterval × U) := fun j => match j with
    | none => {z | (z.2 : X) ∈ Q}
    | some i => {z | (z.2 : X) ∈ closure (O i)}
  let coord (i : κ) (z : P (some i)) : A i × unitInterval :=
    (W i).symm ⟨z.val.2,z.property⟩
  have hc (i : κ) : Continuous (coord i) :=
    (W i).symm.continuous.comp
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _)
  have ht (i : κ) (z : P (some i)) : ((coord i z).2 : ℝ) ≠ 1 / 2 := by
    intro ht
    have hi := (hS i (coord i z)).mpr ht
    have heq : (W i (coord i z) : X) = z.val.2 :=
      congrArg Subtype.val ((W i).apply_symm_apply _)
    rw [heq] at hi
    exact z.val.2.property.2 (mem_iUnion.mpr ⟨i,hi⟩)
  let tm (i : κ) (z : P (some i)) : PuncturedCollarInterval := ⟨(coord i z).2,ht i z⟩
  have htm (i : κ) : Continuous (tm i) := ((hc i).snd).subtype_mk _
  let H : ∀ j, C(P j,X) := fun j => match j with
    | none => ⟨fun z => z.val.2,
        continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)⟩
    | some i => ⟨fun z => W i ((coord i z).1,puncturedCollarSlide z.val.1 (tm i z)),
        continuous_subtype_val.comp ((W i).continuous.comp
          ((hc i).fst.prodMk (continuous_puncturedCollarSlide.comp
            ((continuous_fst.comp continuous_subtype_val).prodMk (htm i)))))⟩
  have hnot (i : κ) (x : closure (O i)) : (x : X) ∈ Q ↔ (x : X) ∉ O i := by
    rw [hQ]
    simp only [mem_sdiff,hCR i x.property,true_and]
    constructor
    · exact fun hx hi => hx (mem_iUnion.mpr ⟨i,hi⟩)
    · intro hx hf
      obtain ⟨j,hj⟩ := mem_iUnion.mp hf
      by_cases he : i = j
      · exact hx (he ▸ hj)
      · exact disjoint_left.mp (hdis he) x.property (subset_closure hj)
  have hfix (i : κ) (z : P (some i)) (hz : (z.val.2 : X) ∈ Q) :
      H (some i) z = z.val.2 := by
    have hn : ¬ ((0 : ℝ) < (coord i z).2 ∧ ((coord i z).2 : ℝ) < 1) := by
      rw [←hO i]
      simpa only [coord,Homeomorph.apply_symm_apply] using
        (hnot i ⟨z.val.2,z.property⟩).mp hz
    have he : (coord i z).2 = 0 ∨ (coord i z).2 = 1 := by
      by_cases hh : ((coord i z).2 : ℝ) = 0
      · exact Or.inl (Subtype.ext hh)
      · right
        apply Subtype.ext
        have hp : (0 : ℝ) < (coord i z).2 :=
          lt_of_le_of_ne (coord i z).2.property.1 (Ne.symm hh)
        exact le_antisymm (coord i z).2.property.2
          (not_lt.mp (fun hh => hn ⟨hp,hh⟩))
    change (W i ((coord i z).1,puncturedCollarSlide z.val.1 (tm i z)) : X) = _
    rw [puncturedCollarSlide_fixed _ _ he]
    exact congrArg Subtype.val ((W i).apply_symm_apply _)
  have hagree : ∀ j k z (hj : z ∈ P j) (hk : z ∈ P k),
      H j ⟨z,hj⟩ = H k ⟨z,hk⟩ := by
    intro j k z hj hk
    cases j with
    | none =>
      cases k with
      | none => rfl
      | some i => exact (hfix i ⟨z,hk⟩ hj).symm
    | some i =>
      cases k with
      | none => exact hfix i ⟨z,hj⟩ hk
      | some j =>
        by_cases he : i = j
        · subst j; rfl
        · exact False.elim (disjoint_left.mp (hdis he) hj hk)
  have hcover : ⋃ j, P j = univ := by
    apply iUnion_eq_univ_iff.mpr
    intro z
    by_cases hz : (z.2 : X) ∈ Q
    · exact ⟨none,hz⟩
    · have hx : (z.2 : X) ∈ ⋃ i, O i := by
        by_contra hn
        exact hz (hQ ▸ ⟨z.2.property.1,hn⟩)
      obtain ⟨i,hi⟩ := mem_iUnion.mp hx
      exact ⟨some i,subset_closure hi⟩
  let G := Set.liftCover P (fun j => H j) hagree hcover
  have hval (j : Option κ) (z : P j) : G z = H j z := Set.liftCover_coe z
  have hG : Continuous G := by
    apply (locallyFinite_of_finite P).continuous hcover
    · intro j
      cases j with
      | none => exact hcQ.preimage (continuous_subtype_val.comp continuous_snd)
      | some i => exact isClosed_closure.preimage (continuous_subtype_val.comp continuous_snd)
    · intro j
      rw [continuousOn_iff_continuous_domRestrict]
      have he : (P j).domRestrict G = H j := funext (hval j)
      rw [he]
      exact (H j).continuous
  have hGU (z : unitInterval × U) : G z ∈ U := by
    obtain ⟨j,hj⟩ := iUnion_eq_univ_iff.mp hcover z
    rw [hval j ⟨z,hj⟩]
    cases j with
    | none => exact z.2.property
    | some i =>
      refine ⟨hCR i (W i _).property,?_⟩
      intro hs
      obtain ⟨j,hj⟩ := mem_iUnion.mp hs
      by_cases hij : i = j
      · subst j
        exact puncturedCollarSlide_ne _ _ ((hS i _).mp hj)
      · exact disjoint_left.mp (hdis hij) (W i _).property (hSC j hj)
  let F : C(unitInterval × U,U) := ⟨fun z => ⟨G z,hGU z⟩,hG.subtype_mk _⟩
  refine ⟨F,?_,?_,?_⟩
  · intro x
    apply Subtype.ext
    obtain ⟨j,hj⟩ := iUnion_eq_univ_iff.mp hcover (0,x)
    change G (0,x) = (x : X)
    rw [hval j ⟨(0,x),hj⟩]
    cases j with
    | none => rfl
    | some i =>
      change (W i ((coord i ⟨(0,x),hj⟩).1,
        puncturedCollarSlide 0 (tm i ⟨(0,x),hj⟩)) : X) = _
      rw [puncturedCollarSlide_zero]
      exact congrArg Subtype.val ((W i).apply_symm_apply _)
  · intro x
    obtain ⟨j,hj⟩ := iUnion_eq_univ_iff.mp hcover (1,x)
    change G (1,x) ∈ Q
    rw [hval j ⟨(1,x),hj⟩]
    cases j with
    | none => exact hj
    | some i =>
      apply (hnot i (W i _)).mpr
      rw [hO i]
      change ¬ ((0 : ℝ) < puncturedCollarSlide 1 (tm i ⟨(1,x),hj⟩) ∧
        (puncturedCollarSlide 1 (tm i ⟨(1,x),hj⟩) : ℝ) < 1)
      rw [puncturedCollarSlide_one]
      unfold puncturedCollarEnd
      split_ifs <;> norm_num
  · intro s x hx
    apply Subtype.ext
    exact hval none ⟨(s,x),hx⟩

end PoincareConjecture.M76
