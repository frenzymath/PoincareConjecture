import PoincareConjecture.Proofs.M76.Mathlib.RectangleCornerArcs

set_option autoImplicit false

open Set Geometry RectangleCornerArcs

namespace RectangleCornerArcs

private theorem zero_interval_pair {t : ℝ} (ht : t ≠ 0) :
    IsFinitePLBallPair ℝ (uIcc 0 t) {0, t} := by
  rcases lt_or_gt_of_ne ht.symm with h | h
  · rw [uIcc_of_le h.le]
    exact isFinitePLBallPair_Icc h
  · rw [uIcc_of_ge h.le, pair_comm]
    exact isFinitePLBallPair_Icc h

theorem vertical_axis_ballPair {z : ℝ} (hz : z ≠ 0) :
    IsFinitePLBallPair ℝ ({(0 : ℝ)} ×ˢ uIcc 0 z) {(0, 0), (0, z)} := by
  let v : ℝ →ᴬ[ℝ] ℝ × ℝ :=
    (ContinuousAffineMap.const ℝ ℝ (0 : ℝ)).prod (ContinuousAffineMap.id ℝ ℝ)
  have hv : Function.Injective v := fun _ _ h => congrArg Prod.snd h
  have hvs : v '' uIcc 0 z = ({0} ×ˢ uIcc 0 z : Set (ℝ × ℝ)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨rfl, hy⟩
    · rintro ⟨hx, hy⟩
      exact ⟨x.2, hy, Prod.ext hx.symm rfl⟩
  have hvval (y : ℝ) : v y = ((0 : ℝ), y) := rfl
  have hvends : v '' {0, z} = {((0 : ℝ), 0), (0, z)} := by
    simpa only [hvval] using image_pair (v : ℝ → ℝ × ℝ) 0 z
  simpa only [hvs, hvends] using (zero_interval_pair hz).affine_image v hv.injOn

theorem horizontal_axis_ballPair {t : ℝ} (ht : t ≠ 0) :
    IsFinitePLBallPair ℝ (uIcc 0 t ×ˢ {(0 : ℝ)}) {(0, 0), (t, 0)} := by
  let h : ℝ →ᴬ[ℝ] ℝ × ℝ :=
    (ContinuousAffineMap.id ℝ ℝ).prod (ContinuousAffineMap.const ℝ ℝ (0 : ℝ))
  have hh : Function.Injective h := fun _ _ heq => congrArg Prod.fst heq
  have hhs : h '' uIcc 0 t = (uIcc 0 t ×ˢ {0} : Set (ℝ × ℝ)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, rfl⟩
    · rintro ⟨hx, hy⟩
      exact ⟨x.1, hx, Prod.ext rfl hy.symm⟩
  have hhval (y : ℝ) : h y = (y, (0 : ℝ)) := rfl
  have hhends : h '' {0, t} = {((0 : ℝ), 0), (t, 0)} := by
    simpa only [hhval] using image_pair (h : ℝ → ℝ × ℝ) 0 t
  simpa only [hhs, hhends] using (zero_interval_pair ht).affine_image h hh.injOn

end RectangleCornerArcs

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem FinitePiecewiseAffineOn.rectangle_corner_patches
    {ψ : (ℝ × ℝ) → E} {T : Set (ℝ × ℝ)}
    (hψ : FinitePiecewiseAffineOn ψ T) (hinj : Function.Injective ψ)
    {a b c d : ℝ} (hab : a ≠ b) (hcd : c ≠ d)
    (hrect : (uIcc a b ×ˢ uIcc c d) ⊆ T) :
    IsFinitePLBallPair (ℝ × ℝ) (ψ '' (uIcc a b ×ˢ uIcc c d))
      ((ψ '' cornerArc a b c d) ∪ (ψ '' cornerArc b a d c)) ∧
    IsFinitePLBallPair ℝ (ψ '' cornerArc a b c d) {ψ (a, d), ψ (b, c)} ∧
    IsFinitePLBallPair ℝ (ψ '' cornerArc b a d c) {ψ (a, d), ψ (b, c)} ∧
    (ψ '' cornerArc a b c d) ∩ (ψ '' cornerArc b a d c) =
      {ψ (a, d), ψ (b, c)} := by
  have hinner : cornerArc a b c d ⊆ T :=
    (cornerArc_subset_rectangle a b c d).trans hrect
  have houter : cornerArc b a d c ⊆ T := by
    apply Subset.trans (cornerArc_subset_rectangle b a d c)
    simpa only [uIcc_comm b a, uIcc_comm d c] using hrect
  have houterPair : IsFinitePLBallPair ℝ (cornerArc b a d c) {(a, d), (b, c)} := by
    simpa only [pair_comm] using cornerArc_ballPair hab.symm hcd.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [image_union] using
      (rectangle_ballPair hab hcd).image_of_subset hψ hrect hinj.injOn
  · simpa only [image_pair] using
      (cornerArc_ballPair hab hcd).image_of_subset hψ hinner hinj.injOn
  · simpa only [image_pair] using houterPair.image_of_subset hψ houter hinj.injOn
  · rw [← image_inter hinj, cornerArc_inter_opposite hab hcd, image_pair]

theorem FinitePiecewiseAffineOn.quadrant_axis_intervals
    {ψ : (ℝ × ℝ) → E} {T : Set (ℝ × ℝ)}
    (hψ : FinitePiecewiseAffineOn ψ T) (hinj : Function.Injective ψ)
    {t z : ℝ} (ht : t ≠ 0) (hz : z ≠ 0)
    (hrect : (uIcc 0 t ×ˢ uIcc 0 z) ⊆ T) :
    IsFinitePLBallPair ℝ (ψ '' ({0} ×ˢ uIcc 0 z)) {ψ 0, ψ (0, z)} ∧
    IsFinitePLBallPair ℝ (ψ '' (uIcc 0 t ×ˢ {0})) {ψ 0, ψ (t, 0)} ∧
    (ψ '' ({0} ×ˢ uIcc 0 z)) ∩ (ψ '' (uIcc 0 t ×ˢ {0})) = {ψ 0} := by
  have hv : ({0} ×ˢ uIcc 0 z : Set (ℝ × ℝ)) ⊆ T := by
    rintro x ⟨hx, hy⟩
    apply hrect
    exact ⟨hx ▸ left_mem_uIcc, hy⟩
  have hh : (uIcc 0 t ×ˢ {0} : Set (ℝ × ℝ)) ⊆ T := by
    rintro x ⟨hx, hy⟩
    apply hrect
    exact ⟨hx, hy ▸ left_mem_uIcc⟩
  have hinter : ({0} ×ˢ uIcc 0 z : Set (ℝ × ℝ)) ∩ (uIcc 0 t ×ˢ {0}) = {0} := by
    ext x
    constructor
    · rintro ⟨hx, hy⟩
      exact Prod.ext hx.1 hy.2
    · rintro rfl
      exact ⟨⟨rfl, left_mem_uIcc⟩, left_mem_uIcc, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa only [image_pair, Prod.zero_eq_mk] using
      (vertical_axis_ballPair hz).image_of_subset hψ hv hinj.injOn
  · simpa only [image_pair, Prod.zero_eq_mk] using
      (horizontal_axis_ballPair ht).image_of_subset hψ hh hinj.injOn
  · rw [← image_inter hinj, hinter, image_singleton]

end Geometry
