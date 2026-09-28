import PoincareConjecture.Proofs.M76.Brown.ClosedCylinderQuotientFibers

set_option autoImplicit false

open Set Metric
open scoped OnePoint

namespace BrownSchoenflies

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X]

omit [NormedSpace ℝ E] in

theorem closedBicollarMap_mem_baseImage_iff
    (e : OpenPartialHomeomorph (sphere (0 : E) 1 × Ioo (-1 : ℝ) 1) X)
    (hes : e.source = univ) (z : sphere (0 : E) 1 × Icc (-1 : ℝ) 1) :
    closedBicollarMap e hes z ∈ bicollarBaseImage e ↔ (z.2 : ℝ) = 0 := by
  change e (closedBicollarCoordinates z) ∈ bicollarBaseImage e ↔ _
  rw [bicollar_apply_mem_baseImage_iff e hes]
  change (z.2 : ℝ) / 2 = 0 ↔ (z.2 : ℝ) = 0
  constructor <;> intro h <;> linarith

theorem closed_cylinder_quotient_regions
    (e : OpenPartialHomeomorph (sphere (0 : E) 1 × Ioo (-1 : ℝ) 1) X)
    (hes : e.source = univ) {A B D : Set X}
    (hcover : A ∪ range (closedBicollarMap e hes) ∪ B = univ)
    (hAend : ∀ z, closedBicollarMap e hes z ∈ A ↔ (z.2 : ℝ) = -1)
    (hBend : ∀ z, closedBicollarMap e hes z ∈ B ↔ (z.2 : ℝ) = 1)
    (hAD : A ⊆ D) (hBD : B ⊆ Dᶜ)
    (hheight : ∀ z, e z ∈ D ↔ (z.2 : ℝ) ≤ 0)
    (q : X → OnePoint E)
    (hqA : ∀ x ∈ A, q x = ((0 : E) : OnePoint E))
    (hqB : ∀ x ∈ B, q x = ∞)
    (hqC : ∀ z, q (closedBicollarMap e hes z) = compactifiedPolar z) :
    (∀ x, q x ∈ ((↑) : E → OnePoint E) '' sphere (0 : E) 1 ↔ x ∈ bicollarBaseImage e) ∧
      ∀ x, q x ∈ ((↑) : E → OnePoint E) '' closedBall (0 : E) 1 ↔ x ∈ D := by
  have hbaseC : bicollarBaseImage e ⊆ range (closedBicollarMap e hes) :=
    (bicollarBaseImage_subset_middle e).trans (middleBicollarBand_subset_closed_range e hes)
  have hAnotbase (x : X) (hx : x ∈ A) : x ∉ bicollarBaseImage e := by
    intro hp
    obtain ⟨z, hz⟩ := hbaseC hp
    have hzA : closedBicollarMap e hes z ∈ A := by rw [hz]; exact hx
    have hzP : closedBicollarMap e hes z ∈ bicollarBaseImage e := by rw [hz]; exact hp
    have htA := (hAend z).mp hzA
    have htP := (closedBicollarMap_mem_baseImage_iff e hes z).mp hzP
    linarith
  have hBnotbase (x : X) (hx : x ∈ B) : x ∉ bicollarBaseImage e := by
    intro hp
    obtain ⟨z, hz⟩ := hbaseC hp
    have hzB : closedBicollarMap e hes z ∈ B := by rw [hz]; exact hx
    have hzP : closedBicollarMap e hes z ∈ bicollarBaseImage e := by rw [hz]; exact hp
    have htB := (hBend z).mp hzB
    have htP := (closedBicollarMap_mem_baseImage_iff e hes z).mp hzP
    linarith
  have hclosedHeight (z : sphere (0 : E) 1 × Icc (-1 : ℝ) 1) :
      closedBicollarMap e hes z ∈ D ↔ (z.2 : ℝ) ≤ 0 := by
    change e (closedBicollarCoordinates z) ∈ D ↔ _
    rw [hheight]
    change (z.2 : ℝ) / 2 ≤ 0 ↔ (z.2 : ℝ) ≤ 0
    constructor <;> intro h <;> linarith
  constructor
  · intro x
    have hxc : x ∈ A ∪ range (closedBicollarMap e hes) ∪ B :=
      hcover.symm.subset (mem_univ x)
    rcases hxc with (hxA | ⟨z, rfl⟩) | hxB
    · rw [hqA x hxA]
      refine iff_of_false ?_ (hAnotbase x hxA)
      rw [OnePoint.coe_injective.mem_set_image, mem_sphere_zero_iff_norm, norm_zero]
      norm_num
    · rw [hqC, compactifiedPolar_mem_sphere_iff, closedBicollarMap_mem_baseImage_iff]
    · rw [hqB x hxB]
      exact iff_of_false OnePoint.infty_notMem_image_coe (hBnotbase x hxB)
  · intro x
    have hxc : x ∈ A ∪ range (closedBicollarMap e hes) ∪ B :=
      hcover.symm.subset (mem_univ x)
    rcases hxc with (hxA | ⟨z, rfl⟩) | hxB
    · rw [hqA x hxA]
      exact iff_of_true ⟨0, by simp, rfl⟩ (hAD hxA)
    · rw [hqC, compactifiedPolar_mem_closedBall_iff, hclosedHeight]
    · rw [hqB x hxB]
      exact iff_of_false OnePoint.infty_notMem_image_coe (hBD hxB)

end BrownSchoenflies
