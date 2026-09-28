import PoincareConjecture.Proofs.M03.Existence.ChartMeasureNative









set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

noncomputable section

universe u

namespace PoincareConjecture.ChartMeasureNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]

local notation "ModelE" => EuclideanSpace ℝ (Fin n)

theorem weightedSourceMeasure_lower (e : OpenPartialHomeomorph M ModelE) (φ : C(M, ℝ))
    {A : Set ModelE} (hA : MeasurableSet A) (hAt : A ⊆ e.target) {c : ℝ≥0∞}
    (hbound : ∀ y ∈ A, c ≤ ENNReal.ofReal (φ (e.symm y))) :
    c • volume.restrict A ≤ weightedSourceMeasure e φ := by
  classical
  calc
    c • volume.restrict A =
        (volume.restrict e.target).withDensity (A.indicator (fun _ => c)) := by
      rw [withDensity_indicator hA, Measure.restrict_restrict_of_subset hAt, withDensity_const]
    _ ≤ weightedSourceMeasure e φ := by
      apply withDensity_mono
      apply Filter.Eventually.of_forall
      intro y
      by_cases hy : y ∈ A
      · simpa only [Set.indicator_of_mem hy] using hbound y hy
      · simp only [Set.indicator_of_notMem hy, zero_le]

theorem weightedChartMeasure_lower (e : OpenPartialHomeomorph M ModelE) (φ : C(M, ℝ))
    {A : Set ModelE} (hA : MeasurableSet A) (hAt : A ⊆ e.target) {c : ℝ≥0∞}
    (hbound : ∀ y ∈ A, c ≤ ENNReal.ofReal (φ (e.symm y))) :
    c • (volume.restrict A).map e.symm ≤ weightedChartMeasure e φ := by
  have h := Measure.map_mono_of_aemeasurable
    (weightedSourceMeasure_lower e φ hA hAt hbound) (chartInverse_aemeasurable e φ)
  simpa only [Measure.map_smul, weightedChartMeasure] using h


theorem exists_local_weightedChartMeasure_lower (e : OpenPartialHomeomorph M ModelE)
    (φ : C(M, ℝ)) {x : M} (hx : x ∈ e.source) (hpos : 0 < φ x) :
    ∃ c : ℝ, 0 < c ∧ ∃ A : Set ModelE, IsOpen A ∧ e x ∈ A ∧ A ⊆ e.target ∧
      ENNReal.ofReal c • (volume.restrict A).map e.symm ≤ weightedChartMeasure e φ := by
  let c : ℝ := φ x / 2
  let A : Set ModelE := e.target ∩ e.symm ⁻¹' {z | c < φ z}
  have hc : 0 < c := half_pos hpos
  have hA : IsOpen A :=
    e.isOpen_inter_preimage_symm (isOpen_lt continuous_const φ.continuous)
  have hxA : e x ∈ A := by
    refine ⟨e.map_source hx, ?_⟩
    change c < φ (e.symm (e x))
    rw [e.left_inv hx]
    exact half_lt_self hpos
  refine ⟨c, hc, A, hA, hxA, Set.inter_subset_left, ?_⟩
  apply weightedChartMeasure_lower e φ hA.measurableSet Set.inter_subset_left
  intro y hy
  exact ENNReal.ofReal_le_ofReal (le_of_lt hy.2)

end PoincareConjecture.ChartMeasureNative
