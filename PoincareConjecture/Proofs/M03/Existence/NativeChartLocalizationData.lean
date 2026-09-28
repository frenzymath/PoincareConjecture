import PoincareConjecture.Proofs.M03.Existence.NativeChartMeasureData
import PoincareConjecture.Proofs.M03.Existence.ChartMeasureDetectionNative









set_option autoImplicit false

open MeasureTheory Set
open scoped Manifold ContDiff ENNReal

noncomputable section

universe u

namespace PoincareConjecture.ChartMeasureNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "ModelE" => EuclideanSpace ℝ (Fin n)

namespace FiniteChartData

variable (d : FiniteChartData (n := n) (M := M))

def sourcePositiveRegion (i : d.centers) (k : ℕ) : Set M :=
  (d.chart i).source ∩ {x | 1 / (k + 1 : ℝ) < d.weight i x}

theorem sourcePositiveRegion_open (i : d.centers) (k : ℕ) :
    IsOpen (d.sourcePositiveRegion i k) :=
  (d.chart i).open_source.inter (isOpen_lt continuous_const (d.weight i).continuous)

theorem map_sourcePositiveRegion (i : d.centers) (k : ℕ) {x : M}
    (hx : x ∈ d.sourcePositiveRegion i k) :
    d.chart i x ∈ positiveRegion (d.chart i) (d.weight i) k := by
  refine ⟨(d.chart i).map_source hx.1, ?_⟩
  change 1 / (k + 1 : ℝ) < d.weight i ((d.chart i).symm (d.chart i x))
  rw [(d.chart i).left_inv hx.1]
  exact hx.2

theorem sourcePositiveRegion_cover :
    Set.univ ⊆ ⋃ ik : d.centers × ℕ, d.sourcePositiveRegion ik.1 ik.2 := by
  intro x _
  obtain ⟨i, hi⟩ := d.exists_weight_pos x
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hi
  apply Set.mem_iUnion.mpr
  refine ⟨(i, k), ?_, hk⟩
  exact d.weight_support_subset i (subset_tsupport (d.weight i) hi.ne')

end FiniteChartData


structure FiniteChartLocalizationData (d : FiniteChartData (n := n) (M := M)) where
  patches : Finset (d.centers × ℕ)
  partition : SmoothPartitionOfUnity patches (𝓡 n) M Set.univ
  support_subset : ∀ a : patches,
    tsupport (partition a) ⊆ d.sourcePositiveRegion a.val.1 a.val.2

namespace FiniteChartLocalizationData

variable {d : FiniteChartData (n := n) (M := M)} (L : FiniteChartLocalizationData d)

def chart (a : L.patches) : OpenPartialHomeomorph M ModelE := d.chart a.val.1

def weight (a : L.patches) : C(M, ℝ) :=
  ⟨L.partition a, (L.partition a).contMDiff.continuous⟩

def region (a : L.patches) : Set ModelE :=
  positiveRegion (L.chart a) (d.weight a.val.1) a.val.2

def lowerConstant (a : L.patches) : ℝ := 1 / (a.val.2 + 1 : ℝ)

def supportImage (a : L.patches) : Set ModelE := L.chart a '' tsupport (L.weight a)

theorem weight_smooth (a : L.patches) : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (L.weight a) :=
  (L.partition a).contMDiff

theorem weight_nonneg (a : L.patches) (x : M) : 0 ≤ L.weight a x :=
  L.partition.nonneg a x

theorem weight_le_one (a : L.patches) (x : M) : L.weight a x ≤ 1 :=
  L.partition.le_one a x

theorem weight_sum (x : M) : (∑ a : L.patches, L.weight a x) = 1 := by
  simpa only [weight, ContinuousMap.coe_mk, finsum_eq_sum_of_fintype] using
    L.partition.sum_eq_one (Set.mem_univ x)

theorem weight_support_source (a : L.patches) :
    tsupport (L.weight a) ⊆ (L.chart a).source :=
  (L.support_subset a).trans Set.inter_subset_left

theorem region_open (a : L.patches) : IsOpen (L.region a) :=
  (L.chart a).isOpen_inter_preimage_symm
    (isOpen_lt continuous_const (d.weight a.val.1).continuous)

theorem region_subset_target (a : L.patches) : L.region a ⊆ (L.chart a).target :=
  Set.inter_subset_left

theorem lowerConstant_pos (a : L.patches) : 0 < L.lowerConstant a :=
  div_pos zero_lt_one (Nat.cast_add_one_pos a.val.2)

theorem supportImage_subset_region (a : L.patches) : L.supportImage a ⊆ L.region a := by
  rintro _ ⟨x, hx, rfl⟩
  exact d.map_sourcePositiveRegion a.val.1 a.val.2 (L.support_subset a hx)

variable [MeasurableSpace M] [BorelSpace M]

theorem region_measure_lower (a : L.patches) :
    ENNReal.ofReal (L.lowerConstant a) • (volume.restrict (L.region a)).map (L.chart a).symm ≤
      d.measure :=
  (positiveRegion_lower (L.chart a) (d.weight a.val.1) a.val.2).trans
    (Measure.le_sum (fun i : d.centers => weightedChartMeasure (d.chart i) (d.weight i)) a.val.1)

variable [CompactSpace M]

theorem supportImage_compact (a : L.patches) : IsCompact (L.supportImage a) :=
  (isClosed_tsupport (L.weight a)).isCompact.image_of_continuousOn
    ((L.chart a).continuousOn.mono (L.weight_support_source a))

end FiniteChartLocalizationData

variable [T2Space M] [CompactSpace M]


theorem exists_finiteChartLocalizationData (d : FiniteChartData (n := n) (M := M)) :
    Nonempty (FiniteChartLocalizationData d) := by
  classical
  let U : d.centers × ℕ → Set M := fun ik => d.sourcePositiveRegion ik.1 ik.2
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U
    (fun ik => d.sourcePositiveRegion_open ik.1 ik.2) d.sourcePositiveRegion_cover
  have hcover : Set.univ ⊆ ⋃ a : s, U a.val := by
    intro x hx
    have hxs := hs hx
    simp only [Set.mem_iUnion] at hxs
    obtain ⟨ik, hiks, hxU⟩ := hxs
    exact Set.mem_iUnion.mpr ⟨⟨ik, hiks⟩, hxU⟩
  obtain ⟨ψ, hψ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓡 n) isClosed_univ
    (fun a : s => U a.val)
    (fun a => d.sourcePositiveRegion_open a.val.1 a.val.2) hcover
  exact ⟨⟨s, ψ, hψ⟩⟩

end PoincareConjecture.ChartMeasureNative
