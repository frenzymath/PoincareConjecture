import PoincareConjecture.Proofs.M38.ProjectiveBallCollarCover
import PoincareConjecture.Proofs.M38.ProjectiveDoubleConnectedSum
import PoincareConjecture.Proofs.M38.FullCutLocalModels

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

theorem exists_projectiveDouble_side_covers
    (A : GeneralizedSliceCarrier.{u}) (C : SmoothProjectiveDoubleModel A.carrier) :
    ∃ (r : ℝ) (f g : RoundCylinderSpace → A.carrier),
      0 < r ∧ r < 1 / 32 ∧
      IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
        (univ ×ˢ Ioo (-1 : ℝ) 1) ∧
      IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ g
        (univ ×ˢ Ioo (-1 : ℝ) 1) ∧
      f '' (univ ×ˢ Ioo (-1 : ℝ) 1) = C.first_region ∧
      g '' (univ ×ˢ Ioo (-1 : ℝ) 1) = C.second_region ∧
      (∀ p, f (-p.1, -p.2) = f p) ∧ (∀ p, g (-p.1, -p.2) = g p) ∧
      (∀ x ∈ univ ×ˢ Ioo (-1 : ℝ) 1, ∀ y ∈ univ ×ˢ Ioo (-1 : ℝ) 1,
        f x = f y ↔ x = y ∨ x = (-y.1, -y.2)) ∧
      (∀ x ∈ univ ×ˢ Ioo (-1 : ℝ) 1, ∀ y ∈ univ ×ˢ Ioo (-1 : ℝ) 1,
        g x = g y ↔ x = y ∨ x = (-y.1, -y.2)) ∧
      (∀ (z : UnitTwoSphere) (t : ℝ), t ∈ Ioo (1 - r) 1 →
        f (z, t) = C.collar (z, 2 * (t - 1))) ∧
      (∀ (z : UnitTwoSphere) (t : ℝ), t ∈ Ioo (1 - r) 1 →
        g (z, t) = C.collar (z, 2 * (1 - t))) := by
  obtain ⟨r₀, B₀, E₀, hr₀, _, h₀⟩ := exists_projectiveDouble_first_filled_side A C
  obtain ⟨r₁, B₁, E₁, hr₁, _, h₁⟩ := exists_projectiveDouble_second_filled_side A C
  obtain ⟨q₀, hq₀, hf₀, _, hi₀, hg₀⟩ := exists_projectiveBall_linear_collar_cover B₀
  obtain ⟨q₁, hq₁, hf₁, _, hi₁, hg₁⟩ := exists_projectiveBall_linear_collar_cover B₁
  let r := min (min (r₀ / 2) (r₁ / 2)) (1 / 64)
  have hr : 0 < r := lt_min (lt_min (half_pos hr₀) (half_pos hr₁)) (by norm_num)
  have hrr₀ : r ≤ r₀ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hrr₁ : r ≤ r₁ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hr64 : r ≤ 1 / 64 := min_le_right _ _
  let f := E₀.map ∘ q₀
  let g := E₁.map ∘ q₁
  have hmem₀ (p : RoundCylinderSpace) (hp : p ∈ univ ×ˢ Ioo (-1 : ℝ) 1) :
      q₀ p ∈ B₀.closedBallᶜ := hi₀.subset (mem_image_of_mem _ hp)
  have hmem₁ (p : RoundCylinderSpace) (hp : p ∈ univ ×ˢ Ioo (-1 : ℝ) 1) :
      q₁ p ∈ B₁.closedBallᶜ := hi₁.subset (mem_image_of_mem _ hp)
  have hl₀ : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-1 : ℝ) 1) := by
    rintro ⟨p, hp⟩
    let e := regionPartialDiffeomorph E₀
      (surgeryBall_closedImage_compact B₀ 1 (by norm_num)).isClosed.isOpen_compl
      C.first_open
    exact (hq₀ p).comp (𝓡 3) A.carrier
      (e.isLocalDiffeomorphAt _ _ _ (hmem₀ p hp))
  have hl₁ : IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ g
      (univ ×ˢ Ioo (-1 : ℝ) 1) := by
    rintro ⟨p, hp⟩
    let e := regionPartialDiffeomorph E₁
      (surgeryBall_closedImage_compact B₁ 1 (by norm_num)).isClosed.isOpen_compl
      C.second_open
    exact (hq₁ p).comp (𝓡 3) A.carrier
      (e.isLocalDiffeomorphAt _ _ _ (hmem₁ p hp))
  refine ⟨r, f, g, hr, by linarith, hl₀, hl₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [image_comp, hi₀, E₀.map_image]
  · rw [image_comp, hi₁, E₁.map_image]
  · intro p
    exact congrArg E₀.map ((hf₀ _ _).mpr (Or.inr rfl))
  · intro p
    exact congrArg E₁.map ((hf₁ _ _).mpr (Or.inr rfl))
  · intro x hx y hy
    change E₀.map (q₀ x) = E₀.map (q₀ y) ↔ _
    exact (E₀.left_inverse.injOn.eq_iff (hmem₀ x hx) (hmem₀ y hy)).trans (hf₀ x y)
  · intro x hx y hy
    change E₁.map (q₁ x) = E₁.map (q₁ y) ↔ _
    exact (E₁.left_inverse.injOn.eq_iff (hmem₁ x hx) (hmem₁ y hy)).trans (hf₁ x y)
  · intro z t ht
    have hs : |2 * (1 - t)| ≤ 1 / 16 := by
      rw [abs_of_pos (by linarith [ht.2])]
      linarith [ht.1, ht.2]
    have ht' : 1 - 2 * (1 - t) / 2 = t := by ring
    have he := hg₀ z (2 * (1 - t)) hs
    rw [ht'] at he
    change E₀.map (q₀ (z, t)) = _
    rw [he, h₀ z (2 * (t - 1)) ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    rw [show 1 + 2 * (1 - t) = 1 - 2 * (t - 1) by ring]
  · intro z t ht
    have hs : |2 * (1 - t)| ≤ 1 / 16 := by
      rw [abs_of_pos (by linarith [ht.2])]
      linarith [ht.1, ht.2]
    have ht' : 1 - 2 * (1 - t) / 2 = t := by ring
    have he := hg₁ z (2 * (1 - t)) hs
    rw [ht'] at he
    change E₁.map (q₁ (z, t)) = _
    rw [he, h₁ z (2 * (1 - t)) ⟨by linarith [ht.2], by linarith [ht.1]⟩]

end PoincareConjecture.M38
