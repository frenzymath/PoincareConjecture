import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralHeightBandSection
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLLevelChartTransport

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem IsFinitePL.exists_original_collar_level_chart
    {B : Set E} {T : Set F} {upper : E → ℝ}
    {C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T}
    (hC : C.IsFinitePL) (A : F → ℝ)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2) {c : ℝ} (hc : 0 ≤ c) :
    ∃ L : {x : E | x ∈ B ∧ c ≤ upper x} ≃ₜ (T ∩ {y | A y = c} : Set F),
      L.IsFinitePL ∧ ∀ x,
        (L x : F) = C ⟨((x : E), c), x.property.1, hc, x.property.2⟩ := by
  have hcopy := hC
  obtain ⟨_, ⟨K, hK, hKs, _⟩, _⟩ := hcopy
  obtain ⟨G, hG, hGval⟩ :=
    K.exists_heightBand_section_chart (lower := fun _ => 0) (upper := upper) hK hKs c
  have hdom : {x : E | x ∈ B ∧ c ∈ Icc 0 (upper x)} =
      {x : E | x ∈ B ∧ c ≤ upper x} := by
    ext x
    simp only [mem_ofPred_eq, mem_Icc, hc, true_and]
  have hsection : K.space ∩ {p : E × ℝ | p.2 = c} =
      {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ∩ {p | p.2 = c} := by
    rw [hKs]
  let G' := (Homeomorph.setCongr hdom.symm).trans (G.trans (Homeomorph.setCongr hsection))
  have hG' : G'.IsFinitePL := hG.setCongr hdom hsection
  have hG'val (x : {x : E | x ∈ B ∧ c ≤ upper x}) :
      (G' x : E × ℝ) = ((x : E), c) := hGval ⟨x, hdom.symm ▸ x.property⟩
  obtain ⟨L, hL, hLval⟩ := hC.transport_level_chart hheight G' hG'
  refine ⟨L, hL, fun x => (hLval x).trans ?_⟩
  apply congrArg (fun p => (C p : F))
  exact Subtype.ext (hG'val x)

end Homeomorph
