import PoincareConjecture.Proofs.M76.Mathlib.CoordinateCylinder
import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineHeightShear
import PoincareConjecture.Proofs.M76.Mathlib.PLBandCutoff










set_option autoImplicit false

open Set Geometry

namespace Geometry

private theorem localPL_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : LocallyPiecewiseAffineOn f univ) :
    LocallyPiecewiseAffineOn (fun y => -f y) univ := by
  intro x hx
  obtain ⟨K, hK, hxK, hKU, hfK⟩ := hf x hx
  refine ⟨K, hK, hxK, hKU, ?_⟩
  intro s hs
  obtain ⟨a, ha⟩ := hfK s hs
  exact ⟨-a, fun y hy => congrArg Neg.neg (ha hy)⟩

private theorem localPL_min {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f g : E → ℝ}
    (hf : LocallyPiecewiseAffineOn f univ) (hg : LocallyPiecewiseAffineOn g univ) :
    LocallyPiecewiseAffineOn (fun y => min (f y) (g y)) univ := by
  apply (localPL_neg ((localPL_neg hf).max (localPL_neg hg))).congr
  intro y _
  change -max (-f y) (-g y) = min (f y) (g y)
  by_cases h : f y ≤ g y
  · rw [max_eq_left (neg_le_neg h), min_eq_left h, neg_neg]
  · rw [max_eq_right (neg_le_neg (le_of_not_ge h)),
      min_eq_right (le_of_not_ge h), neg_neg]

private theorem exists_affine_minimum
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (I : Finset ι) (hI : I.Nonempty)
    (a : ι → E →ᴬ[ℝ] ℝ) :
    ∃ f : E → ℝ, LocallyPiecewiseAffineOn f univ ∧
      (∀ y, ∃ i ∈ I, f y = a i y) ∧
      ∀ y, 0 ≤ f y ↔ ∀ i ∈ I, 0 ≤ a i y := by
  classical
  induction I using Finset.induction_on with
  | empty => exact (Finset.not_nonempty_empty hI).elim
  | @insert i I hi ih =>
    by_cases hne : I.Nonempty
    · obtain ⟨f, hf, hselect, hnonneg⟩ := ih hne
      refine ⟨fun y => min (a i y) (f y),
        localPL_min (locallyPiecewiseAffineOn_affine (a i) isOpen_univ) hf, ?_, ?_⟩
      · intro y
        by_cases hle : a i y ≤ f y
        · exact ⟨i, Finset.mem_insert_self _ _, min_eq_left hle⟩
        · obtain ⟨j, hj, hfj⟩ := hselect y
          exact ⟨j, Finset.mem_insert_of_mem hj, (min_eq_right (le_of_not_ge hle)).trans hfj⟩
      · intro y
        simp only [le_min_iff, hnonneg y, Finset.mem_insert, forall_eq_or_imp]
    · have hIempty : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst I
      refine ⟨a i, locallyPiecewiseAffineOn_affine (a i) isOpen_univ, ?_, ?_⟩
      · intro y
        exact ⟨i, Finset.mem_insert_self _ _, rfl⟩
      · intro y
        simp




theorem exists_coordinateCylinder_halfspace_chart
    {ι : Type*} [Fintype ι] (J : Finset ι) {x : ι → ℝ}
    (hx : x ∈ frontier (coordinateCylinder J)) :
    ∃ (ell : (ι → ℝ) →ᴬ[ℝ] ℝ) (w : ι → ℝ)
      (H : OpenPartialHomeomorph (ι → ℝ) (ι → ℝ)),
      ell.contLinear w = 1 ∧ x ∈ H.source ∧ H x = x ∧ ell x = 0 ∧
      H ∈ piecewiseAffineGroupoid (ι → ℝ) ∧
      ∀ y ∈ H.source, y ∈ coordinateCylinder J ↔ 0 ≤ ell (H y) := by
  classical
  have hxD : x ∈ coordinateCylinder J := (isClosed_coordinateCylinder J).frontier_subset hx
  have hactive : ∃ i ∈ J, |x i| = 1 := by
    by_contra hn
    push Not at hn
    let U : Set (ι → ℝ) := ⋂ i ∈ J, {y | |y i| < 1}
    have hU : IsOpen U := isOpen_biInter_finset fun i _ =>
      isOpen_lt (continuous_apply i).abs continuous_const
    have hxU : x ∈ U := by
      simp only [U, mem_iInter, mem_ofPred_eq]
      exact fun i hi => lt_of_le_of_ne (hxD i hi) (hn i hi)
    have hUD : U ⊆ coordinateCylinder J := by
      intro y hy i hi
      exact (mem_iInter₂.mp hy i hi).le
    exact hx.2 (mem_interior.mpr ⟨U, hUD, hU, hxU⟩)
  let I := J.filter (fun i => |x i| = 1)
  have hI : I.Nonempty := by
    obtain ⟨i, hi, hxi⟩ := hactive
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hxi⟩⟩
  have hsign (i : ι) (hi : i ∈ I) : x i = 1 ∨ x i = -1 :=
    (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp (Finset.mem_filter.mp hi).2
  let a : ι → (ι → ℝ) →ᴬ[ℝ] ℝ := fun i =>
    ContinuousAffineMap.const ℝ (ι → ℝ) 1 -
      x i • (ContinuousLinearMap.proj i).toContinuousAffineMap
  have ha (i : ι) (y : ι → ℝ) : a i y = 1 - x i * y i := rfl
  have haw (i : ι) (hi : i ∈ I) : (a i).contLinear (-x) = 1 := by
    change 0 - x i * (-x i) = 1
    rcases hsign i hi with h | h <;> rw [h] <;> norm_num
  have hax (i : ι) (hi : i ∈ I) : a i x = 0 := by
    rw [ha]
    rcases hsign i hi with h | h <;> rw [h] <;> norm_num
  obtain ⟨f, hf, hselect, hnonneg⟩ := exists_affine_minimum I hI a
  obtain ⟨i0, hi0⟩ := hI
  have hfx : f x = a i0 x := by
    obtain ⟨i, hi, hfi⟩ := hselect x
    rw [hfi, hax i hi, hax i0 hi0]
  obtain ⟨H, hxH, hHx, _, _, hHPL, _, _, hheight⟩ :=
    OpenPartialHomeomorph.exists_finite_affine_height_shear hf convex_univ
      (fun i : {i // i ∈ I} => a i) (-x) (fun i => haw i i.property)
      (fun y _ => by obtain ⟨i, hi, hfi⟩ := hselect y; exact ⟨⟨i, hi⟩, hfi⟩)
      (a i0) (haw i0 hi0) (mem_univ x) hfx
  let U : Set (ι → ℝ) :=
    (⋂ i ∈ J \ I, {y | |y i| < 1}) ∩
      (⋂ i ∈ I, {y | -1 < x i * y i})
  have hU : IsOpen U :=
    (isOpen_biInter_finset fun i _ =>
      isOpen_lt (continuous_apply i).abs continuous_const).inter
    (isOpen_biInter_finset fun i _ =>
      isOpen_lt continuous_const (continuous_const.mul (continuous_apply i)))
  have hxU : x ∈ U := by
    constructor
    · simp only [mem_iInter, mem_ofPred_eq]
      intro i hi
      have hiJ := (Finset.mem_sdiff.mp hi).1
      have hni := (Finset.mem_sdiff.mp hi).2
      exact lt_of_le_of_ne (hxD i hiJ) (fun he => hni (Finset.mem_filter.mpr ⟨hiJ, he⟩))
    · simp only [mem_iInter, mem_ofPred_eq]
      intro i hi
      rcases hsign i hi with h | h <;> rw [h] <;> norm_num
  have hmem (y : ι → ℝ) (hy : y ∈ U) :
      y ∈ coordinateCylinder J ↔ 0 ≤ f y := by
    rw [hnonneg]
    constructor
    · intro hyD i hi
      rw [ha]
      have hib := hyD i (Finset.mem_filter.mp hi).1
      rcases hsign i hi with h | h
      · rw [h, one_mul]
        linarith [(abs_le.mp hib).2]
      · rw [h, neg_one_mul]
        linarith [(abs_le.mp hib).1]
    · intro hfnonneg i hiJ
      by_cases hi : i ∈ I
      · have hp := hfnonneg i hi
        rw [ha] at hp
        have hn : -1 < x i * y i := mem_iInter₂.mp hy.2 i hi
        rcases hsign i hi with h | h
        · rw [h, one_mul] at hp hn
          exact abs_le.mpr ⟨hn.le, by linarith⟩
        · rw [h, neg_one_mul] at hp hn
          exact abs_le.mpr ⟨by linarith, by linarith⟩
      · exact (mem_iInter₂.mp hy.1 i (Finset.mem_sdiff.mpr ⟨hiJ, hi⟩)).le
  refine ⟨a i0, -x, H.restr U, haw i0 hi0,
    ⟨hxH, by simpa only [hU.interior_eq] using hxU⟩, hHx, hax i0 hi0,
    closedUnderRestriction' hHPL hU, ?_⟩
  intro y hy
  change y ∈ coordinateCylinder J ↔ 0 ≤ a i0 (H y)
  rw [hheight y hy.1]
  exact hmem y (interior_subset hy.2)

end Geometry
