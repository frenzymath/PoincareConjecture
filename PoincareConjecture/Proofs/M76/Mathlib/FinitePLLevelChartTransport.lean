import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem IsFinitePL.transport_level_chart {S : Set E} {T : Set F} {B : Set V}
    {H : S ≃ₜ T} (hH : H.IsFinitePL) {r : E → ℝ} {A : F → ℝ}
    (hheight : ∀ p : S, A (H p) = r p) {c : ℝ}
    (L : B ≃ₜ (S ∩ {p | r p = c} : Set E)) (hL : L.IsFinitePL) :
    ∃ G : B ≃ₜ (T ∩ {y | A y = c} : Set F), G.IsFinitePL ∧
      ∀ x : B, (G x : F) = H ⟨L x, (L x).property.1⟩ := by
  have hcopy := hL.symm
  obtain ⟨_, ⟨J, hJ, hJs, _⟩, _⟩ := hcopy
  have hmem (p : S) : (p : E) ∈ S ∩ {p | r p = c} ↔
      (H p : F) ∈ T ∩ {y | A y = c} := by
    change ((p : E) ∈ S ∧ r p = c) ↔ (H p : F) ∈ T ∧ A (H p) = c
    simp only [p.property, (H p).property, hheight p, true_and]
  let R := H.restrictSubsets inter_subset_left inter_subset_left hmem
  have hR : R.IsFinitePL :=
    hH.restrictSubsets inter_subset_left inter_subset_left hmem J hJ hJs
  exact ⟨L.trans R, hL.trans hR, fun _ => rfl⟩

end Homeomorph
