import PoincareConjecture.Proofs.M03.Existence.ChartMeasureComparisonNative










set_option autoImplicit false

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

universe u v

namespace PoincareConjecture.ChartMeasureNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]

local notation "ModelE" => EuclideanSpace ℝ (Fin n)


def positiveRegion (e : OpenPartialHomeomorph M ModelE) (φ : C(M, ℝ)) (k : ℕ) :
    Set ModelE := e.target ∩ e.symm ⁻¹' {x | 1 / (k + 1 : ℝ) < φ x}

theorem positiveRegion_open (e : OpenPartialHomeomorph M ModelE) (φ : C(M, ℝ)) (k : ℕ) :
    IsOpen (positiveRegion e φ k) :=
  e.isOpen_inter_preimage_symm (isOpen_lt continuous_const φ.continuous)

theorem positiveRegion_subset_target (e : OpenPartialHomeomorph M ModelE)
    (φ : C(M, ℝ)) (k : ℕ) : positiveRegion e φ k ⊆ e.target :=
  Set.inter_subset_left

theorem positiveRegion_lower (e : OpenPartialHomeomorph M ModelE) (φ : C(M, ℝ)) (k : ℕ) :
    ENNReal.ofReal (1 / (k + 1 : ℝ)) •
        (volume.restrict (positiveRegion e φ k)).map e.symm ≤
      weightedChartMeasure e φ :=
  weightedChartMeasure_lower e φ (positiveRegion_open e φ k).measurableSet
    (positiveRegion_subset_target e φ k)
    (fun _ hy => ENNReal.ofReal_le_ofReal hy.2.le)


theorem ae_zero_weightedSource_of_positiveRegion
    (e : OpenPartialHomeomorph M ModelE) (φ : C(M, ℝ)) {f : ModelE → ℝ}
    (hzero : ∀ k : ℕ, f =ᵐ[volume.restrict (positiveRegion e φ k)] 0) :
    f =ᵐ[weightedSourceMeasure e φ] 0 := by
  have hcommon : ∀ᵐ y ∂(volume : Measure ModelE),
      ∀ k : ℕ, y ∈ positiveRegion e φ k → f y = 0 := by
    apply ae_all_iff.mpr
    intro k
    exact (ae_restrict_iff' (positiveRegion_open e φ k).measurableSet).mp (hzero k)
  have hdensity : AEMeasurable (fun y => ENNReal.ofReal (φ (e.symm y)))
      (volume.restrict e.target) :=
    ((φ.continuous.comp_continuousOn e.symm.continuousOn).aemeasurable
      e.open_target.measurableSet).ennreal_ofReal
  apply (ae_withDensity_iff' hdensity).mpr
  filter_upwards [ae_restrict_of_ae hcommon, ae_restrict_mem e.open_target.measurableSet]
    with y hy hyt
  intro hnonzero
  have hpos : 0 < φ (e.symm y) :=
    ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hnonzero)
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
  exact hy k ⟨hyt, hk⟩


theorem ae_zero_weightedChart_of_positiveRegion
    (e : OpenPartialHomeomorph M ModelE) (φ : C(M, ℝ)) {f : M → ℝ}
    (hf : Measurable f)
    (hzero : ∀ k : ℕ, f ∘ e.symm =ᵐ[volume.restrict (positiveRegion e φ k)] 0) :
    f =ᵐ[weightedChartMeasure e φ] 0 := by
  apply (ae_map_iff (chartInverse_aemeasurable e φ)
    (measurableSet_eq_fun hf measurable_const)).mpr
  exact ae_zero_weightedSource_of_positiveRegion e φ hzero

variable {iota : Type v} [Finite iota]

theorem ae_zero_sumWeightedChart_of_positiveRegion
    (e : iota → OpenPartialHomeomorph M ModelE) (φ : iota → C(M, ℝ))
    {f : M → ℝ} (hf : Measurable f)
    (hzero : ∀ (i : iota) (k : ℕ),
      f ∘ (e i).symm =ᵐ[volume.restrict (positiveRegion (e i) (φ i) k)] 0) :
    f =ᵐ[Measure.sum (fun i => weightedChartMeasure (e i) (φ i))] 0 := by
  apply Measure.ae_sum_iff.mpr
  intro i
  exact ae_zero_weightedChart_of_positiveRegion (e i) (φ i) hf (hzero i)

end PoincareConjecture.ChartMeasureNative
