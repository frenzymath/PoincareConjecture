import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Lift.HalfSpace
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Relative.Correction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)

theorem exists_supported_lower_lift_preparation
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hzero : ∀ z x, Φ 0 z x = x)
    (hΦ : ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2))
    (hΦinv : ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2))
    (χ : Real → Real) (hχ : ContDiff Real ∞ χ)
    (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = toE3 (Φ (χ (y 2)) (y 2) (toE2 y)) (y 2))
    {a b : Real} (hab : a < b) {C : Set E3} (hC : IsCompact C) :
    ∃ L : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y, L y 2 = y 2) ∧ (∀ y, y 2 ≤ a → L y = y) ∧
      (∀ y, b ≤ y 2 → L y = H y) ∧
      ∃ K : Set E3, IsCompact K ∧
        ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
          (∀ y ∉ K, G y = y) ∧ (∀ y, b ≤ y 2 → G y = y) ∧
          (∀ y ∈ C, G (H y) = L y) ∧ G '' (H '' C) = L '' C := by
  obtain ⟨L, hLheight, hLlow, hLhigh⟩ :=
    exists_parametric_lift_fixed_below Φ hzero hΦ hΦinv χ hχ hab
  have hagree (y : E3) (hy : b ≤ y 2) : L y = H y := (hLhigh y hy).trans (hH y).symm
  let v : E3 := EuclideanSpace.single 2 1
  let l : E3 →L[Real] Real := innerSL Real v
  have hl (y : E3) : l y = y 2 := by simp [l, v, EuclideanSpace.inner_single_left]
  have hheight (y : E3) : l (H y) = l y := by rw [hl, hl, hH]; rfl
  obtain ⟨K, hK, G, hfix, hhalf, hpoint, himage⟩ :=
    exists_supported_correction_of_halfspace_agreement l v (by rw [hl]; simp [v]) b
      H L hheight (fun y hy => hagree y (by change b ≤ l y at hy; rwa [hl] at hy)) hC
  exact ⟨L, hLheight, hLlow, hagree, K, hK, G, hfix,
    fun y hy => hhalf (by change b ≤ l y; rwa [hl]), hpoint, himage⟩

theorem exists_supported_upper_lift_preparation
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hzero : ∀ z x, Φ 0 z x = x)
    (hΦ : ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2))
    (hΦinv : ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2))
    (χ : Real → Real) (hχ : ContDiff Real ∞ χ)
    (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = toE3 (Φ (χ (y 2)) (y 2) (toE2 y)) (y 2))
    {a b : Real} (hab : a < b) {C : Set E3} (hC : IsCompact C) :
    ∃ L : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y, L y 2 = y 2) ∧ (∀ y, b ≤ y 2 → L y = y) ∧
      (∀ y, y 2 ≤ a → L y = H y) ∧
      ∃ K : Set E3, IsCompact K ∧
        ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
          (∀ y ∉ K, G y = y) ∧ (∀ y, y 2 ≤ a → G y = y) ∧
          (∀ y ∈ C, G (H y) = L y) ∧ G '' (H '' C) = L '' C := by
  obtain ⟨L, hLheight, hLhigh, hLlow⟩ :=
    exists_parametric_lift_fixed_above Φ hzero hΦ hΦinv χ hχ hab
  have hagree (y : E3) (hy : y 2 ≤ a) : L y = H y := (hLlow y hy).trans (hH y).symm
  let v : E3 := EuclideanSpace.single 2 (-1)
  let l : E3 →L[Real] Real := innerSL Real v
  have hl (y : E3) : l y = -y 2 := by simp [l, v, EuclideanSpace.inner_single_left]
  have hheight (y : E3) : l (H y) = l y := by rw [hl, hl, hH]; rfl
  obtain ⟨K, hK, G, hfix, hhalf, hpoint, himage⟩ :=
    exists_supported_correction_of_halfspace_agreement l v (by rw [hl]; simp [v]) (-a)
      H L hheight (fun y hy => hagree y (by change -a ≤ l y at hy; rw [hl] at hy; linarith)) hC
  exact ⟨L, hLheight, hLhigh, hagree, K, hK, G, hfix,
    fun y hy => hhalf (by change -a ≤ l y; rw [hl]; linarith), hpoint, himage⟩

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
