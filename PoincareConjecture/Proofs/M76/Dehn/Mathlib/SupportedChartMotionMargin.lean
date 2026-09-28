import PoincareConjecture.Proofs.M76.Mathlib.FinitePositiveHeightGap
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Topology.MetricSpace.Thickening











set_option autoImplicit false

open Set Metric

namespace OpenPartialHomeomorph





theorem exists_supported_motion_margin
    {E X ι : Type*} [MetricSpace E] [TopologicalSpace X] [T2Space X] [Finite ι]
    (Q : OpenPartialHomeomorph E X) {C : Set E}
    (hC : IsCompact C) (hCQ : C ⊆ Q.source)
    (A U : ι → Set X) (hA : ∀ i, IsCompact (A i))
    (hU : ∀ i, IsOpen (U i)) (hAU : ∀ i, A i ⊆ U i) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (H : E → E) (g : X → X),
      EqOn g (Q ∘ H ∘ Q.symm) Q.target → EqOn g id (Q '' C)ᶜ →
      (∀ z ∈ C, dist (H z) z < ε) → ∀ i, MapsTo g (A i) (U i) := by
  classical
  have hB : IsCompact (Q '' C) :=
    hC.image_of_continuousOn (Q.continuousOn.mono hCQ)
  have htarget (i : ι) : A i ∩ Q '' C ⊆ Q.target := by
    rintro x ⟨_, z, hz, rfl⟩
    exact Q.map_source (hCQ hz)
  let T (i : ι) : Set E := Q.symm '' (A i ∩ Q '' C)
  have hT (i : ι) : IsCompact (T i) :=
    ((hA i).inter_right hB.isClosed).image_of_continuousOn
      (Q.symm.continuousOn.mono (htarget i))
  have hTU (i : ι) : T i ⊆ Q.source ∩ Q ⁻¹' U i := by
    rintro z ⟨x, hx, rfl⟩
    refine ⟨Q.map_target (htarget i hx), ?_⟩
    change Q (Q.symm x) ∈ U i
    rw [Q.right_inv (htarget i hx)]
    exact hAU i hx.1
  choose δ hδ hδU using fun i =>
    (hT i).exists_thickening_subset_open (Q.isOpen_inter_preimage (hU i)) (hTU i)
  obtain ⟨ε, hε, hgap⟩ := (Set.toFinite (univ : Set ι)).exists_pos_lt_positive_values
    δ (by norm_num : (0 : ℝ) < 1)
  refine ⟨ε, hε.1, ?_⟩
  intro H g hchart hout hsmall i x hxA
  by_cases hxC : x ∈ Q '' C
  · obtain ⟨z, hz, rfl⟩ := hxC
    have hzT : z ∈ T i :=
      ⟨Q z, ⟨hxA, mem_image_of_mem Q hz⟩, Q.left_inv (hCQ hz)⟩
    have hzU := hδU i (mem_thickening_iff.mpr
      ⟨z, hzT, (hsmall z hz).trans (hgap i (mem_univ i) (hδ i))⟩)
    rw [hchart (Q.map_source (hCQ hz))]
    change Q (H (Q.symm (Q z))) ∈ U i
    rw [Q.left_inv (hCQ hz)]
    exact hzU.2
  · rw [hout hxC]
    exact hAU i hxA

end OpenPartialHomeomorph
