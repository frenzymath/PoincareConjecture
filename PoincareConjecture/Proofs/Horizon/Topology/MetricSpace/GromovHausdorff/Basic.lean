import Mathlib.Topology.MetricSpace.GromovHausdorff
import Mathlib.Order.Zorn

open Set Filter Topology
open scoped Topology

namespace Poincare.GromovHausdorff

universe u

def IsDeltaNet {X : Type*} [MetricSpace X] (δ : ℝ) (x : X) (L : Set X) : Prop :=
  x ∈ L ∧ (∀ y : X, ∃ z ∈ L, dist y z < δ) ∧
    ∃ ε > 0, ∀ ⦃u v : X⦄, u ∈ L → v ∈ L → u ≠ v → ε ≤ dist u v

theorem IsDeltaNet.mono {X : Type*} [MetricSpace X] {x : X} {L : Set X}
    {δ₁ δ₂ : ℝ} (hδ : δ₁ ≤ δ₂) (hL : IsDeltaNet δ₁ x L) :
    IsDeltaNet δ₂ x L := by
  rcases hL with ⟨hx, hcover, hsep⟩
  refine ⟨hx, ?_, hsep⟩
  intro y
  rcases hcover y with ⟨z, hz, hyz⟩
  exact ⟨z, hz, lt_of_lt_of_le hyz hδ⟩

theorem IsDeltaNet.nonempty {X : Type*} [MetricSpace X] {δ : ℝ} {x : X}
    {L : Set X} (hL : IsDeltaNet δ x L) : L.Nonempty :=
  ⟨x, hL.1⟩

theorem exists_isDeltaNet_separated {X : Type*} [MetricSpace X]
    (δ : ℝ) (hδ : 0 < δ) (x : X) :
    ∃ L : Set X,
      x ∈ L ∧
      (∀ y : X, ∃ z ∈ L, dist y z < δ) ∧
      (∀ ⦃u v : X⦄, u ∈ L → v ∈ L → u ≠ v → δ ≤ dist u v) := by
  let P : Set (Set X) :=
    {L | x ∈ L ∧ ∀ ⦃u v : X⦄, u ∈ L → v ∈ L → u ≠ v → δ ≤ dist u v}
  have hstart : ({x} : Set X) ∈ P := by
    constructor
    · exact mem_singleton x
    · intro u v hu hv huv
      have hu' : u = x := mem_singleton_iff.mp hu
      have hv' : v = x := mem_singleton_iff.mp hv
      exact (huv (hu'.trans hv'.symm)).elim
  have hchain : ∀ c ⊆ P, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ P, ∀ s ∈ c, s ⊆ ub := by
    intro c hc hcc hcn
    let ub : Set X := ⋃₀ c
    refine ⟨ub, ?_, ?_⟩
    · constructor
      · obtain ⟨s, hs⟩ := hcn
        exact mem_sUnion_of_mem ((hc hs).1) hs
      · intro u v hu hv huv
        obtain ⟨s, hs, hus⟩ := mem_sUnion.mp hu
        obtain ⟨t, ht, hvt⟩ := mem_sUnion.mp hv
        have horder : s ⊆ t ∨ t ⊆ s := by
          by_cases hst : s = t
          · exact Or.inl (hst ▸ Subset.rfl)
          · exact hcc hs ht hst
        rcases horder with hst | hts
        · exact (hc ht).2 (hst hus) hvt huv
        · exact (hc hs).2 hus (hts hvt) huv
    · intro s hs
      exact subset_sUnion_of_mem hs
  obtain ⟨L, hsub, hmax⟩ := zorn_subset_nonempty P hchain ({x} : Set X) hstart
  have hLP : L ∈ P := hmax.prop
  refine ⟨L, hLP.1, ?_, hLP.2⟩
  intro y
  by_contra hnot
  have hfar : ∀ z ∈ L, δ ≤ dist y z := by
    intro z hz
    exact le_of_not_gt (fun hlt => hnot ⟨z, hz, hlt⟩)
  have hinsert : insert y L ∈ P := by
    refine ⟨mem_insert_of_mem y hLP.1, ?_⟩
    intro u v hu hv huv
    rcases hu with rfl | hu
    · rcases hv with rfl | hv
      · exact (huv rfl).elim
      · exact hfar v hv
    · rcases hv with rfl | hv
      · rw [dist_comm]
        exact hfar u hu
      · exact hLP.2 hu hv huv
  have hEq : insert y L = L := hmax.eq_of_superset hinsert (subset_insert y L)
  have hyL : y ∈ L := by
    rw [← hEq]
    exact mem_insert y L
  exact hnot ⟨y, hyL, by simpa using hδ⟩

theorem exists_isDeltaNet {X : Type*} [MetricSpace X]
    (δ : ℝ) (hδ : 0 < δ) (x : X) :
    ∃ L : Set X, IsDeltaNet δ x L := by
  obtain ⟨L, hx, hcover, hsep⟩ := exists_isDeltaNet_separated δ hδ x
  exact ⟨L, ⟨hx, hcover, ⟨δ, hδ, hsep⟩⟩⟩

structure MetricSpaceBundle where
  carrier : Type*
  metric : MetricSpace carrier

instance (X : MetricSpaceBundle) : MetricSpace X.carrier := X.metric

structure BasedMetricSpaceBundle where
  carrier : Type u
  metric : MetricSpace carrier
  base : carrier

instance (X : BasedMetricSpaceBundle) : MetricSpace X.carrier := X.metric

structure PointedCompactMetricSpace where
  carrier : Type*
  metric : MetricSpace carrier
  compact : CompactSpace carrier
  nonempty : Nonempty carrier
  base : carrier

namespace PointedCompactMetricSpace

instance (X : PointedCompactMetricSpace) : MetricSpace X.carrier := X.metric
instance (X : PointedCompactMetricSpace) : CompactSpace X.carrier := X.compact
instance (X : PointedCompactMetricSpace) : Nonempty X.carrier := X.nonempty

noncomputable def unpointedGH (X Y : PointedCompactMetricSpace) : ℝ :=
  letI : MetricSpace X.carrier := X.metric
  letI : CompactSpace X.carrier := X.compact
  letI : Nonempty X.carrier := X.nonempty
  letI : MetricSpace Y.carrier := Y.metric
  letI : CompactSpace Y.carrier := Y.compact
  letI : Nonempty Y.carrier := Y.nonempty
  _root_.GromovHausdorff.ghDist X.carrier Y.carrier

theorem unpointedGH_nonneg (X Y : PointedCompactMetricSpace) :
    0 ≤ unpointedGH X Y := by
  change 0 ≤ dist (_root_.GromovHausdorff.toGHSpace X.carrier)
    (_root_.GromovHausdorff.toGHSpace Y.carrier)
  exact dist_nonneg

theorem unpointedGH_triangle (X Y Z : PointedCompactMetricSpace) :
    unpointedGH X Z ≤ unpointedGH X Y + unpointedGH Y Z := by
  change dist (_root_.GromovHausdorff.toGHSpace X.carrier)
      (_root_.GromovHausdorff.toGHSpace Z.carrier) ≤
    dist (_root_.GromovHausdorff.toGHSpace X.carrier)
      (_root_.GromovHausdorff.toGHSpace Y.carrier) +
      dist (_root_.GromovHausdorff.toGHSpace Y.carrier)
        (_root_.GromovHausdorff.toGHSpace Z.carrier)
  exact dist_triangle _ _ _

end PointedCompactMetricSpace

def UnpointedGHConverges (X : ℕ → PointedCompactMetricSpace)
    (Y : PointedCompactMetricSpace) : Prop :=
  Tendsto (fun k => PointedCompactMetricSpace.unpointedGH (X k) Y) atTop (𝓝 0)

structure RealizationSequence (X Y : Type u) [MetricSpace X] [MetricSpace Y]
    (x : X) (y : Y) where
  ambient : ℕ → MetricSpaceBundle.{u}
  left : ∀ k, X → (ambient k).carrier
  right : ∀ k, Y → (ambient k).carrier
  left_isometry : ∀ k, Isometry (left k)
  right_isometry : ∀ k, Isometry (right k)
  base_agree : ∀ k, left k x = right k y
  hausdorff_tendsto_zero :
    Tendsto (fun k => @Metric.hausdorffDist (ambient k).carrier inferInstance
      (Set.range (left k)) (Set.range (right k))) atTop (𝓝 0)

structure VaryingRealizationSequence
    (X : ℕ → BasedMetricSpaceBundle.{u}) (Y : BasedMetricSpaceBundle.{u}) where
  ambient : ℕ → MetricSpaceBundle.{u}
  left : ∀ k, (X k).carrier → (ambient k).carrier
  right : ∀ k, Y.carrier → (ambient k).carrier
  left_isometry : ∀ k, Isometry (left k)
  right_isometry : ∀ k, Isometry (right k)
  base_agree : ∀ k, left k (X k).base = right k Y.base
  hausdorff_tendsto_zero :
    Tendsto (fun k => @Metric.hausdorffDist (ambient k).carrier inferInstance
      (Set.range (left k)) (Set.range (right k))) atTop (𝓝 0)

end Poincare.GromovHausdorff
