import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal Manifold ContDiff

noncomputable section

universe u v

namespace PoincareConjecture.ChartMeasureNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]

local notation "ModelE" => EuclideanSpace ℝ (Fin n)

def weightedSourceMeasure (e : OpenPartialHomeomorph M ModelE) (φ : C(M, ℝ)) :
    Measure ModelE :=
  (volume.restrict e.target).withDensity (fun y => ENNReal.ofReal (φ (e.symm y)))

def weightedChartMeasure (e : OpenPartialHomeomorph M ModelE) (φ : C(M, ℝ)) : Measure M :=
  (weightedSourceMeasure e φ).map e.symm

theorem chartInverse_aemeasurable (e : OpenPartialHomeomorph M ModelE) (φ : C(M, ℝ)) :
    AEMeasurable e.symm (weightedSourceMeasure e φ) :=
  (e.symm.continuousOn.aemeasurable e.open_target.measurableSet).mono'
    (withDensity_absolutelyContinuous _ _)

theorem weightedSourceMeasure_le (e : OpenPartialHomeomorph M ModelE) (φ : C(M, ℝ))
    (hcompact : IsCompact (tsupport φ)) (hsupport : tsupport φ ⊆ e.source)
    (hbound : ∀ x, φ x ≤ 1) :
    weightedSourceMeasure e φ ≤ volume.restrict (e '' tsupport φ) := by
  classical
  let K := e '' tsupport φ
  have hK : IsCompact K := hcompact.image_of_continuousOn (e.continuousOn.mono hsupport)
  have hle : weightedSourceMeasure e φ ≤
      (volume.restrict e.target).withDensity (K.indicator (fun _ => 1)) := by
    apply withDensity_mono
    filter_upwards [ae_restrict_mem e.open_target.measurableSet] with y hy
    by_cases hyK : y ∈ K
    · simpa only [Set.indicator_of_mem hyK] using ENNReal.ofReal_le_one.mpr (hbound (e.symm y))
    · have hzero : φ (e.symm y) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hmem
        exact hyK ⟨e.symm y, hmem, e.right_inv hy⟩
      simp only [hzero, ENNReal.ofReal_zero, Set.indicator_of_notMem hyK, le_refl]
  calc
    weightedSourceMeasure e φ ≤
        (volume.restrict e.target).withDensity (K.indicator (fun _ => 1)) := hle
    _ = (volume.restrict e.target).restrict K :=
      withDensity_indicator_one hK.measurableSet
    _ ≤ volume.restrict K := Measure.restrict_mono_measure Measure.restrict_le_self K

theorem weightedSourceMeasure_finite (e : OpenPartialHomeomorph M ModelE) (φ : C(M, ℝ))
    (hcompact : IsCompact (tsupport φ)) (hsupport : tsupport φ ⊆ e.source)
    (hbound : ∀ x, φ x ≤ 1) : IsFiniteMeasure (weightedSourceMeasure e φ) := by
  have hK : IsCompact (e '' tsupport φ) :=
    hcompact.image_of_continuousOn (e.continuousOn.mono hsupport)
  letI : IsFiniteMeasure (volume.restrict (e '' tsupport φ)) :=
    isFiniteMeasure_restrict.mpr hK.measure_ne_top
  exact isFiniteMeasure_of_le _ (weightedSourceMeasure_le e φ hcompact hsupport hbound)

theorem weightedChartMeasure_finite (e : OpenPartialHomeomorph M ModelE) (φ : C(M, ℝ))
    (hcompact : IsCompact (tsupport φ)) (hsupport : tsupport φ ⊆ e.source)
    (hbound : ∀ x, φ x ≤ 1) : IsFiniteMeasure (weightedChartMeasure e φ) := by
  letI := weightedSourceMeasure_finite e φ hcompact hsupport hbound
  exact Measure.isFiniteMeasure_map _ _

theorem weightedChartMeasure_open_ne_zero (e : OpenPartialHomeomorph M ModelE) (φ : C(M, ℝ))
    (hsupport : tsupport φ ⊆ e.source) {U : Set M} (hU : IsOpen U)
    {x : M} (hxU : x ∈ U) (hpos : 0 < φ x) : weightedChartMeasure e φ U ≠ 0 := by
  have hxsource : x ∈ e.source := hsupport (subset_tsupport _ (ne_of_gt hpos))
  let V : Set ModelE := e.target ∩ e.symm ⁻¹' (U ∩ {z | 0 < φ z})
  have hVopen : IsOpen V :=
    e.isOpen_inter_preimage_symm (hU.inter (isOpen_lt continuous_const φ.continuous))
  have hVnonempty : V.Nonempty := by
    refine ⟨e x, e.map_source hxsource, ?_⟩
    change e.symm (e x) ∈ U ∧ 0 < φ (e.symm (e x))
    rw [e.left_inv hxsource]
    exact ⟨hxU, hpos⟩
  have hdensity : AEMeasurable (fun y => ENNReal.ofReal (φ (e.symm y)))
      (volume.restrict e.target) :=
    ((φ.continuous.comp_continuousOn e.symm.continuousOn).aemeasurable
      e.open_target.measurableSet).ennreal_ofReal
  intro hzero
  rw [weightedChartMeasure, Measure.map_apply_of_aemeasurable
    (chartInverse_aemeasurable e φ) hU.measurableSet] at hzero
  have hnull := (withDensity_apply_eq_zero' hdensity).mp hzero
  rw [Measure.restrict_apply' e.open_target.measurableSet] at hnull
  have hVnull : volume V = 0 := by
    apply measure_mono_null _ hnull
    intro y hy
    exact ⟨⟨ne_of_gt (ENNReal.ofReal_pos.mpr hy.2.2), hy.2.1⟩, hy.1⟩
  exact hVopen.measure_ne_zero volume hVnonempty hVnull

variable {iota : Type v} [Finite iota]

theorem sumWeightedChartMeasure_finite
    (e : iota → OpenPartialHomeomorph M ModelE) (φ : iota → C(M, ℝ))
    (hcompact : ∀ i, IsCompact (tsupport (φ i)))
    (hsupport : ∀ i, tsupport (φ i) ⊆ (e i).source)
    (hbound : ∀ i x, φ i x ≤ 1) :
    IsFiniteMeasure (Measure.sum (fun i => weightedChartMeasure (e i) (φ i))) := by
  letI (i : iota) : IsFiniteMeasure (weightedChartMeasure (e i) (φ i)) :=
    weightedChartMeasure_finite (e i) (φ i) (hcompact i) (hsupport i) (hbound i)
  infer_instance

theorem sumWeightedChartMeasure_openPos
    (e : iota → OpenPartialHomeomorph M ModelE) (φ : iota → C(M, ℝ))
    (hsupport : ∀ i, tsupport (φ i) ⊆ (e i).source)
    (hcover : ∀ x : M, ∃ i, 0 < φ i x) :
    (Measure.sum (fun i => weightedChartMeasure (e i) (φ i))).IsOpenPosMeasure := by
  constructor
  intro U hU hUne hzero
  obtain ⟨x, hx⟩ := hUne
  obtain ⟨i, hi⟩ := hcover x
  apply weightedChartMeasure_open_ne_zero (e i) (φ i) (hsupport i) hU hx hi
  apply le_antisymm _ bot_le
  exact (Measure.le_sum (fun i => weightedChartMeasure (e i) (φ i)) i U).trans hzero.le

variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M] [CompactSpace M]

include n in

theorem exists_finite_openPos_measure :
    ∃ μ : Measure M, IsFiniteMeasure μ ∧ μ.IsOpenPosMeasure := by
  classical
  let U : M → Set M := fun x => (chartAt ModelE x).source
  have hcover : Set.univ ⊆ ⋃ x : M, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, mem_chart_source ModelE x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U
    (fun x => (chartAt ModelE x).open_source) hcover
  let e : s → OpenPartialHomeomorph M ModelE := fun i => chartAt ModelE i.1
  have hfiniteCover : Set.univ ⊆ ⋃ i : s, (e i).source := by
    intro x hx
    have hxs := hs hx
    simp only [Set.mem_iUnion] at hxs
    obtain ⟨y, hys, hxy⟩ := hxs
    exact Set.mem_iUnion.mpr ⟨⟨y, hys⟩, hxy⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓡 n)
    isClosed_univ (fun i : s => (e i).source) (fun i => (e i).open_source) hfiniteCover
  let φ : s → C(M, ℝ) := fun i => ⟨ρ i, (ρ i).contMDiff.continuous⟩
  refine ⟨Measure.sum (fun i : s => weightedChartMeasure (e i) (φ i)), ?_, ?_⟩
  · exact sumWeightedChartMeasure_finite e φ (fun i => (isClosed_tsupport (φ i)).isCompact)
      hρ (fun i x => ρ.le_one i x)
  · exact sumWeightedChartMeasure_openPos e φ hρ
      (fun x => ρ.exists_pos_of_mem (Set.mem_univ x))

end PoincareConjecture.ChartMeasureNative
