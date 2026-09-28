import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSegmentHeightChart
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLGluing
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets

set_option autoImplicit false

open Set Geometry

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_finitePL_corner_height_chart
    (A : E →ᵃ[ℝ] ℝ) {u q v : E} (hu : A u < 0) (hq : A q = 0) (hv : 0 < A v) :
    ∃ d : Icc (A u) (A v) ≃ₜ (segment ℝ u q ∪ segment ℝ q v : Set E),
      d.IsFinitePL ∧ (∀ t, A (d t) = (t : ℝ)) ∧
      (d ⟨A u, ⟨le_rfl, (hu.trans hv).le⟩⟩ : E) = u ∧
      (d ⟨0, ⟨hu.le, hv.le⟩⟩ : E) = q ∧
      (d ⟨A v, ⟨(hu.trans hv).le, le_rfl⟩⟩ : E) = v := by
  obtain ⟨e, he, heA, heu, heq⟩ := A.exists_finitePL_segment_height_chart hu rfl hq
  obtain ⟨f, hf, hfA, hfq, hfv⟩ := A.exists_finitePL_segment_height_chart hv hq rfl
  have hunion : Icc (A u) (0 : ℝ) ∪ Icc 0 (A v) = Icc (A u) (A v) :=
    Icc_union_Icc_eq_Icc hu.le hv.le
  have hI := isFinitePLBallPair_Icc (hu.trans hv)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hI
  have hKunion : K.space = Icc (A u) 0 ∪ Icc 0 (A v) := hKs.trans hunion.symm
  have hoverlap (t : Icc (A u) (0 : ℝ)) :
      (t : ℝ) ∈ Icc 0 (A v) ↔ (e t : E) ∈ segment ℝ q v := by
    constructor
    · intro ht
      have ht0 : (t : ℝ) = 0 := le_antisymm t.property.2 ht.1
      have hte : (e t : E) = q := by
        have hs : t = ⟨0, ⟨hu.le, le_rfl⟩⟩ := Subtype.ext ht0
        rw [hs]
        exact heq
      rw [hte]
      exact left_mem_segment ℝ q v
    · intro ht
      have hAt := mem_image_of_mem A ht
      rw [image_segment, hq, segment_eq_Icc hv.le, heA] at hAt
      exact hAt
  have hagree (t : ℝ) (ht : t ∈ Icc (A u) 0) (ht' : t ∈ Icc 0 (A v)) :
      (e ⟨t, ht⟩ : E) = f ⟨t, ht'⟩ := by
    have ht0 : t = 0 := le_antisymm ht.2 ht'.1
    subst t
    exact heq.trans hfq.symm
  obtain ⟨H, hH, hHe, hHf⟩ :=
    Homeomorph.exists_union_of_isFinitePL e f he hf K hK hKunion hoverlap hagree
  let d := (Homeomorph.setCongr hunion.symm).trans (H.trans (Homeomorph.setCongr rfl))
  refine ⟨d, hH.setCongr hunion rfl, ?_, ?_, ?_, ?_⟩
  · intro t
    rcases hunion.symm.subset t.property with ht | ht
    · exact (congrArg A (hHe ⟨t, ht⟩)).trans (heA ⟨t, ht⟩)
    · exact (congrArg A (hHf ⟨t, ht⟩)).trans (hfA ⟨t, ht⟩)
  · exact (hHe ⟨A u, ⟨le_rfl, hu.le⟩⟩).trans heu
  · exact (hHe ⟨0, ⟨hu.le, le_rfl⟩⟩).trans heq
  · exact (hHf ⟨A v, ⟨hv.le, le_rfl⟩⟩).trans hfv

end AffineMap
