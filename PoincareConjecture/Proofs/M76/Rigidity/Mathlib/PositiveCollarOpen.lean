import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Constructions









set_option autoImplicit false

open Set

variable {E X : Type*} [TopologicalSpace X]



theorem isOpen_positive_collar {B : Set E} {K : Set X} (c : E × ℝ → X)
    (hinside : MapsTo c (B ×ˢ Icc 0 1) K)
    (hproper : ∀ z : (B ×ˢ Icc (0 : ℝ) 1 : Set (E × ℝ)),
      c z ∈ frontier K ↔ (z : E × ℝ).2 = 0)
    {δ : ℝ} (hδ1 : δ ≤ 1)
    (hopen : IsOpen ((Subtype.val : K → X) ⁻¹' (c '' (B ×ˢ Ico 0 δ)))) :
    IsOpen (c '' (B ×ˢ Ioo 0 δ)) ∧
      c '' (B ×ˢ Ioo 0 δ) = (c '' (B ×ˢ Ico 0 δ)) ∩ interior K := by
  have hfull : B ×ˢ Ico (0 : ℝ) δ ⊆ B ×ˢ Icc 0 1 := by
    intro z hz
    exact ⟨hz.1, hz.2.1, hz.2.2.le.trans hδ1⟩
  have heq : c '' (B ×ˢ Ioo 0 δ) = (c '' (B ×ˢ Ico 0 δ)) ∩ interior K := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzU : z ∈ B ×ˢ Ico (0 : ℝ) δ := ⟨hz.1, hz.2.1.le, hz.2.2⟩
      refine ⟨⟨z, hzU, rfl⟩, (mem_interior_iff_notMem_frontier (hinside (hfull hzU))).mpr ?_⟩
      exact fun h => hz.2.1.ne' ((hproper ⟨z, hfull hzU⟩).mp h)
    · rintro ⟨⟨z, hz, rfl⟩, hxint⟩
      have ht : z.2 ≠ 0 := by
        intro ht
        exact ((hproper ⟨z, hfull hz⟩).mpr ht).2 hxint
      exact ⟨z, ⟨hz.1, lt_of_le_of_ne hz.2.1 (Ne.symm ht), hz.2.2⟩, rfl⟩
  refine ⟨?_, heq⟩
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.mp hopen
  have hlocal : (c '' (B ×ˢ Ico 0 δ)) ∩ interior K = O ∩ interior K := by
    ext x
    constructor
    · intro hx
      exact ⟨(Set.ext_iff.mp hOU ⟨x, interior_subset hx.2⟩).mpr hx.1, hx.2⟩
    · intro hx
      exact ⟨(Set.ext_iff.mp hOU ⟨x, interior_subset hx.2⟩).mp hx.1, hx.2⟩
  rw [heq, hlocal]
  exact hO.inter isOpen_interior
