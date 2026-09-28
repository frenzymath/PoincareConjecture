import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

theorem ContMDiffOn.exists_global_extension_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {k : ENat} {f : ℝ → M} {U : Set ℝ} {a b : ℝ}
    (hf : ContMDiffOn 𝓘(ℝ) I k f U) (hab : a ≤ b)
    (hU : IsOpen U) (hI : Icc a b ⊆ U) :
    ∃ g : ℝ → M, ContMDiff 𝓘(ℝ) I k g ∧ EqOn g f (Icc a b) := by
  obtain ⟨la, ra, ha, hUa⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hU.mem_nhds (hI (left_mem_Icc.mpr hab)))
  obtain ⟨lb, rb, hb, hUb⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hU.mem_nhds (hI (right_mem_Icc.mpr hab)))
  have hVI : Icc a b ⊆ Ioo la rb := by
    intro t ht
    exact ⟨ha.1.trans_le ht.1, ht.2.trans_lt hb.2⟩
  have hVU : Ioo la rb ⊆ U := by
    intro t ht
    by_cases hta : t < a
    · exact hUa ⟨ht.1, hta.trans ha.2⟩
    by_cases hbt : b < t
    · exact hUb ⟨hb.1.trans hbt, ht.2⟩
    exact hI ⟨le_of_not_gt hta, le_of_not_gt hbt⟩
  obtain ⟨φ, hzero, hone, hφ⟩ := exists_contMDiffMap_zero_one_of_isClosed
    𝓘(ℝ) (n := k) isOpen_Ioo.isClosed_compl isClosed_Icc
      (disjoint_left.mpr (fun _ ht hi => ht (hVI hi)))
  let ρ : ℝ → ℝ := fun t => (1 - φ t) * a + φ t * t
  have hρ : ContMDiff 𝓘(ℝ) 𝓘(ℝ) k ρ :=
    ((contMDiff_const.sub φ.contMDiff).mul contMDiff_const).add
      (φ.contMDiff.mul contMDiff_id)
  have hρV (t : ℝ) : ρ t ∈ Ioo la rb := by
    by_cases ht : t ∈ Ioo la rb
    · simpa only [ρ, smul_eq_mul] using
        (convex_Ioo la rb) (hVI (left_mem_Icc.mpr hab)) ht
          (sub_nonneg.mpr (hφ t).2) (hφ t).1 (sub_add_cancel 1 (φ t))
    · have hz : φ t = 0 := hzero ht
      simpa only [ρ, hz, sub_zero, one_mul, zero_mul, add_zero] using
        hVI (left_mem_Icc.mpr hab)
  refine ⟨f ∘ ρ, hf.comp_contMDiff hρ (fun t => hVU (hρV t)), ?_⟩
  intro t ht
  have ho : φ t = 1 := hone ht
  simp only [Function.comp_apply, ρ, ho, sub_self, zero_mul, one_mul, zero_add]
