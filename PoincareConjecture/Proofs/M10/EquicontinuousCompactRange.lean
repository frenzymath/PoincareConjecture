import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set Filter Metric
open scoped Topology

namespace PoincareConjecture.M10

variable {A X ι : Type*} [TopologicalSpace A] [MetricSpace X]

theorem isClosed_totallyBounded_fibers {f : ι → A → X} (hf : Equicontinuous f) :
    IsClosed {a | TotallyBounded (range (fun i ↦ f i a))} := by
  apply isClosed_of_closure_subset
  intro a ha
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  have hnear := Metric.equicontinuousAt_iff_right.mp (hf a) (ε / 2) (half_pos hε)
  obtain ⟨b, hbnear, hb⟩ := mem_closure_iff_nhds.mp ha _ hnear
  obtain ⟨S, hS, hcover⟩ := Metric.totallyBounded_iff.mp hb (ε / 2) (half_pos hε)
  refine ⟨S, hS, ?_⟩
  rintro _ ⟨i, rfl⟩
  obtain ⟨y, hy, hdist⟩ := mem_iUnion₂.mp (hcover (mem_range_self i))
  apply mem_iUnion₂.mpr ⟨y, hy, ?_⟩
  change dist (f i a) y < ε
  have hdy : dist (f i b) y < ε / 2 := hdist
  exact lt_of_le_of_lt (dist_triangle _ (f i b) _) (by linarith [hbnear i])

variable [CompleteSpace X] [LocallyCompactSpace X]

theorem exists_compact_range_nhds {f : ι → A → X} {a : A}
    (hf : EquicontinuousAt f a) (ha : TotallyBounded (range (fun i ↦ f i a))) :
    ∃ K : Set X, IsCompact K ∧ ∀ᶠ b in 𝓝 a, ∀ i, f i b ∈ K := by
  have hc : IsCompact (closure (range (fun i ↦ f i a))) :=
    ha.closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨δ, hδ, hK⟩ := hc.exists_isCompact_cthickening
  refine ⟨cthickening δ (closure (range (fun i ↦ f i a))), hK, ?_⟩
  filter_upwards [Metric.equicontinuousAt_iff_right.mp hf δ hδ] with b hb
  intro i
  apply mem_cthickening_of_dist_le _ (f i a) _ _ (subset_closure (mem_range_self i))
  simpa only [dist_comm] using (hb i).le

theorem isOpen_totallyBounded_fibers {f : ι → A → X} (hf : Equicontinuous f) :
    IsOpen {a | TotallyBounded (range (fun i ↦ f i a))} := by
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  obtain ⟨K, hK, hnear⟩ := exists_compact_range_nhds (hf a) ha
  filter_upwards [hnear] with b hb
  exact hK.totallyBounded.subset (range_subset_iff.mpr hb)

theorem exists_compact_range_of_anchored_equicontinuous
    [CompactSpace A] [PreconnectedSpace A] {f : ι → A → X}
    (hf : Equicontinuous f) (a₀ : A) (p : X) (hanchor : ∀ i, f i a₀ = p) :
    ∃ K : Set X, IsCompact K ∧ ∀ i a, f i a ∈ K := by
  classical
  have hanchor' : TotallyBounded (range (fun i ↦ f i a₀)) := by
    apply (isCompact_singleton (x := p)).totallyBounded.subset
    rintro _ ⟨i, rfl⟩
    exact mem_singleton_iff.mpr (hanchor i)
  have hall : {a | TotallyBounded (range (fun i ↦ f i a))} = univ :=
    IsClopen.eq_univ ⟨isClosed_totallyBounded_fibers hf,
      isOpen_totallyBounded_fibers hf⟩ ⟨a₀, hanchor'⟩
  have hlocal (a : A) : ∃ K : Set X, IsCompact K ∧
      ∀ᶠ b in 𝓝 a, ∀ i, f i b ∈ K :=
    exists_compact_range_nhds (hf a) (by
      change a ∈ {b | TotallyBounded (range (fun i ↦ f i b))}
      rw [hall]
      trivial)
  choose K hK hnear using hlocal
  obtain ⟨s, hs⟩ := finite_cover_nhds hnear
  refine ⟨⋃ a ∈ s, K a, s.isCompact_biUnion (fun a _ ↦ hK a), ?_⟩
  intro i a
  have ha : a ∈ ⋃ b ∈ s, {c | ∀ j, f j c ∈ K b} := by rw [hs]; trivial
  obtain ⟨b, hb, hab⟩ := mem_iUnion₂.mp ha
  exact mem_iUnion₂.mpr ⟨b, hb, hab i⟩

end PoincareConjecture.M10
