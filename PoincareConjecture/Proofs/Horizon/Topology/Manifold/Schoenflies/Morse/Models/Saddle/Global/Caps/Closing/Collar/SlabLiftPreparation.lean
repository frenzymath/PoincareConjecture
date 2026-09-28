import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.LiftPreparation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem exists_supported_slab_lift_preparation
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hzero : ∀ z x, Φ 0 z x = x)
    (hΦ : ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2))
    (hΦinv : ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2))
    (χ : Real → Real) (hχ : ContDiff Real ∞ χ)
    (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = toE3 (Φ (χ (y 2)) (y 2) (toE2 y)) (y 2))
    {a b c d : Real} (hab : a < b) (hcd : c < d)
    {C : Set E3} (hC : IsCompact C) :
    ∃ τ : Real → Real, ContDiff Real ∞ τ ∧ EqOn τ χ (Icc b c) ∧
    ∃ L : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y, L y = toE3 (Φ (τ (y 2)) (y 2) (toE2 y)) (y 2)) ∧
      (∀ y, L y 2 = y 2) ∧
      (∀ y, y 2 ≤ a ∨ d ≤ y 2 → L y = y) ∧
      EqOn L H {y | y 2 ∈ Icc b c} ∧
      ∃ K : Set E3, IsCompact K ∧
        ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
          (∀ y ∉ K, G y = y) ∧ EqOn G id {y | y 2 ∈ Icc b c} ∧
          (∀ y ∈ C, G (H y) = L y) ∧ G '' (H '' C) = L '' C := by
  let α : Real → Real := fun z => Real.smoothTransition ((z - a) / (b - a))
  let β : Real → Real := fun z => Real.smoothTransition ((d - z) / (d - c))
  have hα : ContDiff Real ∞ α := Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const (b - a))
  have hβ : ContDiff Real ∞ β := Real.smoothTransition.contDiff.comp
    ((contDiff_const.sub contDiff_id).div_const (d - c))
  have hα0 (z : Real) (hz : z ≤ a) : α z = 0 :=
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_pos.mpr hab).le)
  have hα1 (z : Real) (hz : b ≤ z) : α z = 1 :=
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith))
  have hβ0 (z : Real) (hz : d ≤ z) : β z = 0 :=
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_pos.mpr hcd).le)
  have hβ1 (z : Real) (hz : z ≤ c) : β z = 1 :=
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ (sub_pos.mpr hcd)).mpr (by linarith))
  let τ₁ : Real → Real := fun z => α z * χ z
  let τ₂ : Real → Real := fun z => β z * τ₁ z
  have hτ₁ : ContDiff Real ∞ τ₁ := hα.mul hχ
  have hτ₂ : ContDiff Real ∞ τ₂ := hβ.mul hτ₁
  obtain ⟨L₁, hL₁, _, hh₁, _⟩ := exists_height_lift (fun z => Φ (τ₁ z) z)
    (hΦ.comp ((hτ₁.comp contDiff_fst).prodMk contDiff_id))
    (hΦinv.comp ((hτ₁.comp contDiff_fst).prodMk contDiff_id))
  obtain ⟨L, hL, _, hh, _⟩ := exists_height_lift (fun z => Φ (τ₂ z) z)
    (hΦ.comp ((hτ₂.comp contDiff_fst).prodMk contDiff_id))
    (hΦinv.comp ((hτ₂.comp contDiff_fst).prodMk contDiff_id))
  have hagree₁ (y : E3) (hy : b ≤ y 2) : L₁ y = H y := by
    rw [hL₁, hH]
    simp only [τ₁, hα1 _ hy, one_mul]
  have hagree₂ (y : E3) (hy : y 2 ≤ c) : L y = L₁ y := by
    rw [hL, hL₁]
    simp only [τ₂, hβ1 _ hy, one_mul]
  let v : E3 := EuclideanSpace.single 2 1
  let l : E3 →L[Real] Real := innerSL Real v
  have hl (y : E3) : l y = y 2 := by simp [l, v, EuclideanSpace.inner_single_left]
  have hheight (y : E3) : l (H y) = l y := by rw [hl, hl, hH]; rfl
  obtain ⟨K₁, hK₁, G₁, hfix₁, hhalf₁, hpoint₁, _⟩ :=
    exists_supported_correction_of_halfspace_agreement l v (by rw [hl]; simp [v]) b
      H L₁ hheight (fun y hy => hagree₁ y (by change b ≤ l y at hy; rwa [hl] at hy)) hC
  obtain ⟨K₂, hK₂, G₂, hfix₂, hhalf₂, hpoint₂, _⟩ :=
    exists_supported_correction_of_halfspace_agreement (-l) (-v)
      (by simp [hl, v]) (-c) L₁ L
      (fun y => by change -l (L₁ y) = -l y; rw [hl, hl, hh₁])
      (fun y hy => hagree₂ y (by change -c ≤ -l y at hy; rw [hl] at hy; linarith))
      hC
  let G := G₁.trans G₂
  have hpoint (y : E3) (hy : y ∈ C) : G (H y) = L y := by
    change G₂ (G₁ (H y)) = L y
    rw [hpoint₁ y hy, hpoint₂ y hy]
  refine ⟨τ₂, hτ₂, ?_, L, hL, hh, ?_, ?_, K₁ ∪ K₂, hK₁.union hK₂,
    G, ?_, ?_, hpoint, ?_⟩
  · intro z hz
    simp only [τ₂, τ₁, hα1 z hz.1, hβ1 z hz.2, one_mul]
  · intro y hy
    have ht : τ₂ (y 2) = 0 := by
      rcases hy with hy | hy
      · simp only [τ₂, τ₁, hα0 _ hy, zero_mul, mul_zero]
      · simp only [τ₂, hβ0 _ hy, zero_mul]
    rw [hL, ht, hzero]
    ext i
    fin_cases i <;> rfl
  · intro y hy
    exact (hagree₂ y hy.2).trans (hagree₁ y hy.1)
  · intro y hy
    have hn : y ∉ K₁ ∧ y ∉ K₂ := ⟨fun h => hy (Or.inl h), fun h => hy (Or.inr h)⟩
    change G₂ (G₁ y) = y
    rw [hfix₁ _ hn.1, hfix₂ _ hn.2]
  · intro y hy
    change G₂ (G₁ y) = y
    rw [hhalf₁ (by change b ≤ l y; rw [hl]; exact hy.1)]
    exact hhalf₂ (by change -c ≤ -l y; rw [hl]; linarith [hy.2])
  · rw [image_image]
    exact image_congr hpoint

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
