import PoincareConjecture.Proofs.M03.Existence.ChartMeasureNative









set_option autoImplicit false

open MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

universe u

namespace PoincareConjecture.ChartMeasureNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "ModelE" => EuclideanSpace ℝ (Fin n)


structure FiniteChartData where
  centers : Finset M
  partition : SmoothPartitionOfUnity centers (𝓡 n) M Set.univ
  support_subset : ∀ i : centers, tsupport (partition i) ⊆ (chartAt ModelE i.val).source

namespace FiniteChartData

variable (d : FiniteChartData (n := n) (M := M))

def chart (i : d.centers) : OpenPartialHomeomorph M ModelE := chartAt ModelE i.val

def weight (i : d.centers) : C(M, ℝ) :=
  ⟨d.partition i, (d.partition i).contMDiff.continuous⟩

theorem weight_smooth (i : d.centers) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (d.weight i) :=
  (d.partition i).contMDiff

theorem weight_support_subset (i : d.centers) : tsupport (d.weight i) ⊆ (d.chart i).source :=
  d.support_subset i

theorem weight_nonneg (i : d.centers) (x : M) : 0 ≤ d.weight i x :=
  d.partition.nonneg i x

theorem weight_le_one (i : d.centers) (x : M) : d.weight i x ≤ 1 :=
  d.partition.le_one i x

theorem weight_sum (x : M) : (∑ i : d.centers, d.weight i x) = 1 := by
  simpa only [weight, ContinuousMap.coe_mk, finsum_eq_sum_of_fintype] using
    d.partition.sum_eq_one (Set.mem_univ x)

theorem exists_weight_pos (x : M) : ∃ i : d.centers, 0 < d.weight i x :=
  d.partition.exists_pos_of_mem (Set.mem_univ x)

variable [MeasurableSpace M] [BorelSpace M]


def measure : Measure M :=
  Measure.sum (fun i : d.centers => weightedChartMeasure (d.chart i) (d.weight i))

@[simp] theorem measure_eq : d.measure =
    Measure.sum (fun i : d.centers => weightedChartMeasure (chartAt ModelE i.val) (d.weight i)) := rfl

instance measure_openPos : d.measure.IsOpenPosMeasure :=
  sumWeightedChartMeasure_openPos d.chart d.weight d.weight_support_subset d.exists_weight_pos

variable [CompactSpace M]

theorem weight_compactSupport (i : d.centers) : IsCompact (tsupport (d.weight i)) :=
  (isClosed_tsupport (d.weight i)).isCompact

instance measure_finite : IsFiniteMeasure d.measure :=
  sumWeightedChartMeasure_finite d.chart d.weight d.weight_compactSupport
    d.weight_support_subset d.weight_le_one

end FiniteChartData

variable [T2Space M] [CompactSpace M]


theorem exists_finiteChartData : Nonempty (FiniteChartData (n := n) (M := M)) := by
  classical
  let U : M → Set M := fun x => (chartAt ModelE x).source
  have hcover : Set.univ ⊆ ⋃ x : M, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, mem_chart_source ModelE x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U
    (fun x => (chartAt ModelE x).open_source) hcover
  have hfiniteCover : Set.univ ⊆ ⋃ i : s, (chartAt ModelE i.val).source := by
    intro x hx
    have hxs := hs hx
    simp only [Set.mem_iUnion] at hxs
    obtain ⟨y, hys, hxy⟩ := hxs
    exact Set.mem_iUnion.mpr ⟨⟨y, hys⟩, hxy⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓡 n)
    isClosed_univ (fun i : s => (chartAt ModelE i.val).source)
    (fun i => (chartAt ModelE i.val).open_source) hfiniteCover
  exact ⟨⟨s, ρ, hρ⟩⟩

end PoincareConjecture.ChartMeasureNative
