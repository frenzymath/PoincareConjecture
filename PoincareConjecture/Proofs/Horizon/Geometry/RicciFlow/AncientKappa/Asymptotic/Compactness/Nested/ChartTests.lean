import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Carrier
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

theorem exists_compact_tests_of_isOpen
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
    {U : Set X} (hU : IsOpen U) :
    ∃ A : ℕ → Set X, (∀ m, IsCompact (A m)) ∧ (∀ m, A m ⊆ U) ∧ Monotone A ∧
      ∀ K, IsCompact K → K ⊆ U → ∃ m, K ⊆ A m := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let E := CompactExhaustion.choice U
  refine ⟨fun m => Subtype.val '' E m, fun m => (E.isCompact m).image continuous_subtype_val,
    fun _ _ hx => ?_, fun i j hij => image_mono (E.subset hij), ?_⟩
  · rcases hx with ⟨x, _, rfl⟩
    exact x.property
  · intro K hK hKU
    have hpre : IsCompact ((Subtype.val : U → X) ⁻¹' K) := by
      apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
      rwa [image_preimage_eq_of_subset (by simpa only [Subtype.range_coe] using hKU)]
    obtain ⟨m, hm⟩ := E.exists_superset_of_isCompact hpre
    exact ⟨m, fun x hx => ⟨⟨x, hKU hx⟩, hm hx, rfl⟩⟩

namespace FlowCarrier

attribute [local instance] topologicalSpace chartedSpace isManifold secondCountable

theorem exists_countable_chart_cover {n : ℕ} (C : FlowCarrier n) :
    ∃ q : ℕ → C.carrier, ∀ x : C.carrier, ∃ i, x ∈ (extChartAt (𝓡 n) (q i)).source := by
  classical
  obtain ⟨s, hsc, hs⟩ := countable_cover_nhds
    (fun x : C.carrier => extChartAt_source_mem_nhds (I := 𝓡 n) x)
  obtain ⟨p, _⟩ := C.connected.nonempty
  let t := insert p s
  have htc : t.Countable := hsc.insert p
  let : Countable t := htc.to_subtype
  let : Nonempty t := ⟨⟨p, mem_insert p s⟩⟩
  obtain ⟨q, hq⟩ := exists_surjective_nat t
  refine ⟨fun i => q i, fun x => ?_⟩
  have hx : x ∈ ⋃ y ∈ s, (extChartAt (𝓡 n) y).source := hs.symm ▸ mem_univ x
  rcases mem_iUnion.mp hx with ⟨y, hy⟩
  rcases mem_iUnion.mp hy with ⟨hys, hxy⟩
  obtain ⟨i, hi⟩ := hq ⟨y, mem_insert_of_mem p hys⟩
  exact ⟨i, by simpa only [hi] using hxy⟩

structure CompactChartTests {n : ℕ} (C : FlowCarrier n) where
  center : ℕ → C.carrier
  covers : ∀ x : C.carrier, ∃ i, x ∈ (extChartAt (𝓡 n) (center i)).source
  compact : ℕ → ℕ → Set (ℝ × EuclideanSpace ℝ (Fin n))
  isCompact : ∀ i m, IsCompact (compact i m)
  subset : ∀ i m, compact i m ⊆ Iio 1 ×ˢ (extChartAt (𝓡 n) (center i)).target
  monotone : ∀ i, Monotone (compact i)
  cofinal : ∀ i K, IsCompact K →
    K ⊆ Iio 1 ×ˢ (extChartAt (𝓡 n) (center i)).target → ∃ m, K ⊆ compact i m

theorem nonempty_compactChartTests {n : ℕ} (C : FlowCarrier n) :
    Nonempty C.CompactChartTests := by
  classical
  obtain ⟨q, hq⟩ := C.exists_countable_chart_cover
  have htest (i : ℕ) := exists_compact_tests_of_isOpen
    (X := ℝ × EuclideanSpace ℝ (Fin n))
    ((isOpen_Iio (a := (1 : ℝ))).prod (isOpen_extChartAt_target (I := 𝓡 n) (q i)))
  choose A hA hAU hmono hcofinal using htest
  exact ⟨⟨q, hq, A, hA, hAU, hmono, hcofinal⟩⟩

noncomputable def compactChartTests {n : ℕ} (C : FlowCarrier n) : C.CompactChartTests :=
  Classical.choice C.nonempty_compactChartTests

end FlowCarrier
end PoincareConjecture
