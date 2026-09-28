import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderMiddleModel
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderEndRegions

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.OpenCylinderModel

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {U : Set M}

theorem exists_high_midlevel_model (T : OpenCylinderModel U)
    (R : M → ℝ) (hR : ContinuousOn R U)
    (hnegative : ∃ B : ℝ, ∀ x ∈ T.tail false (1 / 2), R x ≤ B)
    (hdiverge : ∀ B : ℝ, ∃ a ∈ Ioo (0 : ℝ) 1,
      ∀ x ∈ T.tail true a, B < R x) (B : ℝ) :
    ∃ Z : OpenCylinderModel U,
      (∃ C : ℝ, ∀ x ∈ Z.tail false (1 / 2), R x ≤ C) ∧
      (∀ C : ℝ, ∃ a ∈ Ioo (0 : ℝ) 1, ∀ x ∈ Z.tail true a, C < R x) ∧
      ∀ x ∈ Z.tail true (1 / 2), B < R x := by
  obtain ⟨d, hd, hhigh⟩ := hdiverge B
  let c := max d (1 / 2 : ℝ)
  have hc : c ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_lt_of_le (by norm_num) (le_max_right _ _), max_lt hd.2 (by norm_num)⟩
  obtain ⟨Z, _hcoordinate, hinverse, hhalf⟩ := T.exists_midlevel_model hc
  refine ⟨Z, ?_, ?_, ?_⟩
  · obtain ⟨C0, hC0⟩ := hnegative
    obtain ⟨C1, hC1⟩ := (T.isCompact_compactSlab
      (by norm_num : (0 : ℝ) < 1 / 2) hc.2).bddAbove_image
        (hR.mono (T.compactSlab_subset (by norm_num) hc.2))
    refine ⟨max C0 C1, ?_⟩
    intro x hx
    have hxZ := (Z.mem_tail_iff_m28 false (by norm_num) (by norm_num)).mp hx
    have hxle : (T.inverse x).2 ≤ c := by
      by_contra! hnot
      have hh := (hhalf x hxZ.1).mpr hnot
      exact (not_lt_of_ge hh.le) hxZ.2
    by_cases hlow : (T.inverse x).2 < 1 / 2
    · exact (hC0 x ((T.mem_tail_iff_m28 false (by norm_num) (by norm_num)).mpr
        ⟨hxZ.1, hlow⟩)).trans (le_max_left _ _)
    · have hslab : x ∈ T.compactSlab (1 / 2) c :=
        (T.mem_compactSlab_iff (by norm_num) hc.2).mpr
          ⟨hxZ.1, le_of_not_gt hlow, hxle⟩
      exact (hC1 (mem_image_of_mem R hslab)).trans (le_max_right _ _)
  · intro C
    obtain ⟨e, he, hC⟩ := hdiverge C
    have hbeta : 1 - c ∈ Ioo (0 : ℝ) 1 := ⟨sub_pos.mpr hc.2, by linarith [hc.1]⟩
    let a := Poincare.unitIntervalReparam (1 - c) e
    have ha : a ∈ Ioo (0 : ℝ) 1 :=
      (Poincare.unitIntervalReparam_properties hbeta).2.1 he
    refine ⟨a, ha, ?_⟩
    intro x hx
    have hxZ := (Z.mem_tail_iff_m28 true ha.1 ha.2).mp hx
    have hh : Poincare.unitIntervalReparam (1 - c) e <
        Poincare.unitIntervalReparam (1 - c) (T.inverse x).2 := by
      simpa only [hinverse, if_true, a] using hxZ.2
    have hold := ((Poincare.unitIntervalReparam_strictMonoOn hbeta).lt_iff_lt
      he (T.inverse_mem x hxZ.1).2).mp hh
    exact hC x ((T.mem_tail_iff_m28 true he.1 he.2).mpr ⟨hxZ.1, hold⟩)
  · intro x hx
    have hxZ := (Z.mem_tail_iff_m28 true (by norm_num) (by norm_num)).mp hx
    have hheight := (hhalf x hxZ.1).mp hxZ.2
    exact hhigh x ((T.mem_tail_iff_m28 true hd.1 hd.2).mpr
      ⟨hxZ.1, (le_max_left _ _).trans_lt hheight⟩)

end PoincareConjecture.OpenCylinderModel
