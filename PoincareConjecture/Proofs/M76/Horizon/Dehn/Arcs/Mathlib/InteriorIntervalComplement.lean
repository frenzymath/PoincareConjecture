import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervalMiddle










set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn




theorem exists_complementary_end_intervals
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {J W : Set E} {a b u v : E}
    (hJ : IsFinitePLBallPair ℝ J {a, b}) (hW : IsFinitePLBallPair ℝ W {u, v})
    (hWJ : W ⊆ J) (hab : a ≠ b) (huv : u ≠ v)
    (hends : Disjoint W {a, b}) :
    ∃ (L R : Set E) (c d : E),
      ({c, d} : Set E) = {u, v} ∧ c ≠ d ∧
      IsFinitePLBallPair ℝ L {a, c} ∧ IsFinitePLBallPair ℝ R {d, b} ∧
      Disjoint L R ∧ (L ∪ W) ∪ R = J ∧ L ∩ W = {c} ∧ W ∩ R = {d} := by
  obtain ⟨e, he, hea, heb⟩ := hJ.exists_unitInterval_chart_with_endpoints hab
  obtain ⟨f, hf, hval⟩ := he
  have hi : InjOn f (Icc (0 : ℝ) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (e.injective (Subtype.ext
      ((hval ⟨x, hx⟩).trans (hxy.trans (hval ⟨y, hy⟩).symm))))
  have himage : f '' Icc (0 : ℝ) 1 = J := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hval ⟨x, hx⟩ ▸ (e ⟨x, hx⟩).property
    · intro hy
      refine ⟨e.symm ⟨y, hy⟩, (e.symm ⟨y, hy⟩).property, ?_⟩
      exact (hval _).symm.trans (congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩))
  have hf0 : f 0 = a := (hval 0).symm.trans hea
  have hf1 : f 1 = b := (hval 1).symm.trans heb
  let tu := e.symm ⟨u, hWJ (hW.1 (Or.inl rfl))⟩
  let tv := e.symm ⟨v, hWJ (hW.1 (Or.inr rfl))⟩
  have htu : f tu = u :=
    (hval tu).symm.trans (congrArg Subtype.val (e.apply_symm_apply _))
  have htv : f tv = v :=
    (hval tv).symm.trans (congrArg Subtype.val (e.apply_symm_apply _))
  have htne : (tu : ℝ) ≠ tv := by
    intro h
    exact huv (htu.symm.trans ((congrArg f h).trans htv))
  let α : ℝ := min tu tv
  let β : ℝ := max tu tv
  have hαβ : α < β := min_lt_max.mpr htne
  have hα : α ∈ Icc (0 : ℝ) 1 :=
    ⟨le_min tu.property.1 tv.property.1, (min_le_left _ _).trans tu.property.2⟩
  have hβ : β ∈ Icc (0 : ℝ) 1 :=
    ⟨tu.property.1.trans (le_max_left _ _), max_le tu.property.2 tv.property.2⟩
  have hpair : ({f α, f β} : Set E) = {u, v} := by
    rcases le_total (tu : ℝ) tv with h | h
    · simp only [α, β, min_eq_left h, max_eq_right h, htu, htv]
    · simp only [α, β, min_eq_right h, max_eq_left h, htu, htv, pair_comm]
  have hαW : f α ∈ W := hW.1 (hpair.subset (Or.inl rfl))
  have hβW : f β ∈ W := hW.1 (hpair.subset (Or.inr rfl))
  have h0α : 0 < α := by
    by_contra h
    have heq : α = 0 := le_antisymm (le_of_not_gt h) hα.1
    exact Set.disjoint_left.mp hends hαW (by rw [heq, hf0]; exact Or.inl rfl)
  have hβ1 : β < 1 := by
    by_contra h
    have heq : β = 1 := le_antisymm hβ.2 (le_of_not_gt h)
    exact Set.disjoint_left.mp hends hβW (by rw [heq, hf1]; exact Or.inr rfl)
  have hmiddle : Icc α β ⊆ Icc (0 : ℝ) 1 :=
    fun _ ht => ⟨hα.1.trans ht.1, ht.2.trans hβ.2⟩
  have hleft : Icc 0 α ⊆ Icc (0 : ℝ) 1 :=
    fun _ ht => ⟨ht.1, ht.2.trans hα.2⟩
  have hright : Icc β 1 ⊆ Icc (0 : ℝ) 1 :=
    fun _ ht => ⟨hβ.1.trans ht.1, ht.2⟩
  have hWimage : W = f '' Icc α β := by
    have hW' : IsFinitePLBallPair ℝ W {f α, f β} := hpair.symm ▸ hW
    exact hW'.eq_image_Icc_of_subset hf hi hαβ hmiddle (hWJ.trans himage.symm.subset)
  refine ⟨f '' Icc 0 α, f '' Icc β 1, f α, f β, hpair,
    fun h => hαβ.ne (hi hα hβ h), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [image_pair, hf0] using
      (isFinitePLBallPair_Icc h0α).image_of_subset hf hleft hi
  · simpa only [image_pair, hf1] using
      (isFinitePLBallPair_Icc hβ1).image_of_subset hf hright hi
  · apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    have heq := hi (hright hy) (hleft hx) hyx
    have hβα := hy.1.trans (heq ▸ hx.2)
    exact hαβ.not_ge hβα
  · have hcover : (Icc 0 α ∪ Icc α β) ∪ Icc β 1 = Icc (0 : ℝ) 1 := by
      rw [Icc_union_Icc_eq_Icc h0α.le hαβ.le,
        Icc_union_Icc_eq_Icc hβ.1 hβ1.le]
    rw [hWimage, ← image_union, ← image_union, hcover, himage]
  · have hinter : Icc 0 α ∩ Icc α β = ({α} : Set ℝ) := by
      ext t
      constructor
      · intro ht
        exact le_antisymm ht.1.2 ht.2.1
      · rintro rfl
        exact ⟨⟨hα.1, le_rfl⟩, ⟨le_rfl, hαβ.le⟩⟩
    have hmap : f '' (Icc 0 α ∩ Icc α β) = f '' Icc 0 α ∩ f '' Icc α β :=
      image_inter_on fun x hx y hy hxy => hi (hmiddle hx) (hleft hy) hxy
    rw [hWimage, ← hmap, hinter, image_singleton]
  · have hinter : Icc α β ∩ Icc β 1 = ({β} : Set ℝ) := by
      ext t
      constructor
      · intro ht
        exact le_antisymm ht.1.2 ht.2.1
      · rintro rfl
        exact ⟨⟨hαβ.le, le_rfl⟩, ⟨le_rfl, hβ.2⟩⟩
    have hmap : f '' (Icc α β ∩ Icc β 1) = f '' Icc α β ∩ f '' Icc β 1 :=
      image_inter_on fun x hx y hy hxy => hi (hright hx) (hmiddle hy) hxy
    rw [hWimage, ← hmap, hinter, image_singleton]

end PoincareConjecture.M76.Dehn
