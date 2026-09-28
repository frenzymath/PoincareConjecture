import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Compactness.Lindelof

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace Poincare.HausdorffDensity

theorem euclideanHausdorffMeasure_image_le
    {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} {s : Set X} {K : ℝ≥0} (hf : LipschitzOnWith K f s) (n : ℕ) :
    Measure.euclideanHausdorffMeasure n (f '' s) ≤
      (K : ℝ≥0∞) ^ n * Measure.euclideanHausdorffMeasure n s := by
  simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply,
    ENNReal.smul_def, smul_eq_mul]
  rw [mul_left_comm ((K : ℝ≥0∞) ^ n)]
  gcongr
  simpa only [ENNReal.rpow_natCast] using hf.hausdorffMeasure_image_le
    (show (0 : ℝ) ≤ n by positivity)

theorem measure_le_of_locally_le
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ ν : Measure X} {s : Set X} (hs : MeasurableSet s)
    (h : ∀ x ∈ s, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ t, MeasurableSet t → t ⊆ U ∩ s → μ t ≤ ν t) :
    μ s ≤ ν s := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  let : Nonempty s := hne.to_subtype
  choose U hUo hUx hU using fun x : s ↦ h x x.property
  obtain ⟨a, ha⟩ := (HereditarilyLindelofSpace.isLindelof s).indexed_countable_subcover U hUo
    (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, hUx ⟨x, hx⟩⟩)
  let V : ℕ → Set X := fun i ↦ U (a i) ∩ s
  have hVm (i : ℕ) : MeasurableSet (V i) := (hUo _).measurableSet.inter hs
  have hcover : (⋃ i, V i) = s := by
    apply Subset.antisymm
    · exact iUnion_subset fun i ↦ inter_subset_right
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (ha hx)
      exact mem_iUnion.mpr ⟨i, hi, hx⟩
  have hDm (i : ℕ) : MeasurableSet (disjointed V i) := MeasurableSet.disjointed hVm i
  have hD (i : ℕ) : μ (disjointed V i) ≤ ν (disjointed V i) :=
    hU (a i) _ (hDm i) (disjointed_le V i)
  rw [← hcover, ← iUnion_disjointed (f := V),
    measure_iUnion (disjoint_disjointed V) hDm,
    measure_iUnion (disjoint_disjointed V) hDm]
  exact ENNReal.tsum_le_tsum hD

theorem le_of_forall_one_lt_pow_mul {a b : ℝ≥0∞} (m : ℕ)
    (h : ∀ K : ℝ≥0, 1 < K → a ≤ (K : ℝ≥0∞) ^ m * b) : a ≤ b := by
  have ht : Tendsto (fun K : ℝ≥0 ↦ (K : ℝ≥0∞) ^ m * b) (𝓝[>] 1) (𝓝 b) := by
    have ht := ENNReal.Tendsto.mul_const (b := b) (f := 𝓝[>] (1 : ℝ≥0))
      (ENNReal.Tendsto.pow (n := m)
        (ENNReal.continuous_coe.continuousAt.mono_left nhdsWithin_le_nhds))
      (Or.inl (by simp : ((1 : ℝ≥0) : ℝ≥0∞) ^ m ≠ 0))
    simpa using ht
  exact ge_of_tendsto ht (by filter_upwards [self_mem_nhdsWithin] with K hK using h K hK)

theorem measure_eq_of_locally_approx
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ ν : Measure X} {s : Set X} (hs : MeasurableSet s) (m : ℕ)
    (h : ∀ K : ℝ≥0, 1 < K → ∀ x ∈ s, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∀ t, MeasurableSet t → t ⊆ U ∩ s →
        μ t ≤ (K : ℝ≥0∞) ^ m * ν t ∧ ν t ≤ (K : ℝ≥0∞) ^ m * μ t) :
    μ s = ν s := by
  apply le_antisymm
  · apply le_of_forall_one_lt_pow_mul m
    intro K hK
    change μ s ≤ ((K : ℝ≥0∞) ^ m • ν) s
    apply measure_le_of_locally_le hs
    intro x hx
    obtain ⟨U, hUo, hUx, hU⟩ := h K hK x hx
    exact ⟨U, hUo, hUx, fun t ht hts ↦ (hU t ht hts).1⟩
  · apply le_of_forall_one_lt_pow_mul m
    intro K hK
    change ν s ≤ ((K : ℝ≥0∞) ^ m • μ) s
    apply measure_le_of_locally_le hs
    intro x hx
    obtain ⟨U, hUo, hUx, hU⟩ := h K hK x hx
    exact ⟨U, hUo, hUx, fun t ht hts ↦ (hU t ht hts).2⟩

end Poincare.HausdorffDensity
