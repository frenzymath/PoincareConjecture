import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UnitInterval










set_option autoImplicit false

open Set

namespace Homeomorph




theorem surjective_of_interval_endpoints
    {X : Type*} [TopologicalSpace X] (b : Icc (0 : ℝ) 1 ≃ₜ X)
    {f : Icc (0 : ℝ) 1 → X} (hf : Continuous f)
    (hzero : f ⟨0, ⟨le_rfl, zero_le_one⟩⟩ = b ⟨0, ⟨le_rfl, zero_le_one⟩⟩)
    (hone : f ⟨1, ⟨zero_le_one, le_rfl⟩⟩ = b ⟨1, ⟨zero_le_one, le_rfl⟩⟩) :
    Function.Surjective f := by
  let g : Icc (0 : ℝ) 1 → ℝ := fun t => b.symm (f t)
  have hg : Continuous g := continuous_subtype_val.comp (b.symm.continuous.comp hf)
  have hgzero : g ⟨0, ⟨le_rfl, zero_le_one⟩⟩ = 0 := by
    simp only [g, hzero, b.symm_apply_apply]
  have hgone : g ⟨1, ⟨zero_le_one, le_rfl⟩⟩ = 1 := by
    simp only [g, hone, b.symm_apply_apply]
  have hcover : Icc (0 : ℝ) 1 ⊆ range g :=
    (isPreconnected_range hg).Icc_subset
      ⟨⟨0, ⟨le_rfl, zero_le_one⟩⟩, hgzero⟩
      ⟨⟨1, ⟨zero_le_one, le_rfl⟩⟩, hgone⟩
  intro x
  obtain ⟨t, ht⟩ := hcover (b.symm x).property
  exact ⟨t, b.symm.injective (Subtype.ext ht)⟩

end Homeomorph
