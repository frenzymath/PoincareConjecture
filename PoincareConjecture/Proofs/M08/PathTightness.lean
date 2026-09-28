import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Tactic.Linarith









set_option autoImplicit false

open Set Filter Topology
open scoped BoundedContinuousFunction

namespace PoincareConjecture.M08

private theorem compact_fiber_neighborhood {A X ι : Type*}
    [TopologicalSpace A] [MetricSpace X] [CompleteSpace X] [LocallyCompactSpace X]
    (f : ι → A → X) {t : A} (hf : EquicontinuousAt f t)
    (ht : TotallyBounded (Set.range (fun i ↦ f i t))) :
    ∃ U ∈ 𝓝 t, ∃ K : Set X, IsCompact K ∧ ∀ s ∈ U, ∀ i, f i s ∈ K := by
  have hcompact := ht.closure.isCompact_of_isClosed isClosed_closure
  obtain ⟨δ, hδ, hK⟩ := hcompact.exists_isCompact_cthickening
  have hnear := Metric.equicontinuousAt_iff_right.mp hf δ hδ
  refine ⟨{s | ∀ i, dist (f i t) (f i s) < δ}, hnear,
    Metric.cthickening δ (closure (Set.range (fun i ↦ f i t))), hK, ?_⟩
  intro s hs i
  exact Metric.mem_cthickening_of_dist_le _ (f i t) _ _
    (subset_closure (Set.mem_range_self i)) (by simpa only [dist_comm] using (hs i).le)


theorem totallyBounded_fibers_of_anchored {A X ι : Type*}
    [TopologicalSpace A] [PreconnectedSpace A]
    [MetricSpace X] [CompleteSpace X] [LocallyCompactSpace X]
    (f : ι → A → X) (hf : Equicontinuous f) (a : A) (x : X)
    (ha : ∀ i, f i a = x) : ∀ t, TotallyBounded (Set.range (fun i ↦ f i t)) := by
  let P : Set A := {t | TotallyBounded (Set.range (fun i ↦ f i t))}
  have hclosed : IsClosed P := by
    apply isClosed_of_closure_subset
    intro t ht
    apply Metric.totallyBounded_iff.mpr
    intro ε hε
    have hnear := Metric.equicontinuousAt_iff_right.mp (hf t) (ε / 2) (half_pos hε)
    obtain ⟨s, hsP, hst⟩ :=
      ((mem_closure_iff_frequently.mp ht).and_eventually hnear).exists
    obtain ⟨N, hNfinite, hN⟩ := Metric.totallyBounded_iff.mp hsP (ε / 2) (half_pos hε)
    refine ⟨N, hNfinite, ?_⟩
    rintro _ ⟨i, rfl⟩
    obtain ⟨z, hz, hiz⟩ := Set.mem_iUnion₂.mp (hN (Set.mem_range_self i))
    refine Set.mem_iUnion₂.mpr ⟨z, hz, ?_⟩
    change dist (f i t) z < ε
    have hsum := (dist_triangle (f i t) (f i s) z).trans_lt
      (add_lt_add (hst i) hiz)
    simpa only [add_halves] using hsum
  have hopen : IsOpen P := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    obtain ⟨U, hU, K, hK, hUK⟩ := compact_fiber_neighborhood f (hf t) ht
    apply Filter.mem_of_superset hU
    intro s hs
    exact hK.totallyBounded.subset (by rintro _ ⟨i, rfl⟩; exact hUK s hs i)
  have haP : a ∈ P := by
    apply (totallyBounded_singleton (a := x)).subset
    rintro _ ⟨i, rfl⟩
    exact Set.mem_singleton_iff.mpr (ha i)
  have hP : P = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨a, haP⟩
  intro t
  change t ∈ P
  rw [hP]
  exact Set.mem_univ t


theorem exists_compact_range_of_anchored {A X ι : Type*}
    [TopologicalSpace A] [CompactSpace A] [PreconnectedSpace A]
    [MetricSpace X] [CompleteSpace X] [LocallyCompactSpace X]
    (f : ι → A → X) (hf : Equicontinuous f) (a : A) (x : X)
    (ha : ∀ i, f i a = x) :
    ∃ K : Set X, IsCompact K ∧ ∀ i t, f i t ∈ K := by
  have hfibers := totallyBounded_fibers_of_anchored f hf a x ha
  choose U hU K hK hUK using fun t ↦ compact_fiber_neighborhood f (hf t) (hfibers t)
  obtain ⟨S, hS⟩ := finite_cover_nhds hU
  refine ⟨⋃ t ∈ S, K t, S.isCompact_biUnion (fun t _ ↦ hK t), ?_⟩
  intro i t
  have ht : t ∈ ⋃ s ∈ S, U s := hS.symm ▸ Set.mem_univ t
  obtain ⟨s, hs, hts⟩ := Set.mem_iUnion₂.mp ht
  exact Set.mem_iUnion₂.mpr ⟨s, hs, hUK s t hts i⟩


theorem exists_uniform_subsequence_of_anchored {A X : Type*}
    [TopologicalSpace A] [CompactSpace A] [PreconnectedSpace A]
    [MetricSpace X] [CompleteSpace X] [LocallyCompactSpace X]
    (f : ℕ → A → X) (hf : Equicontinuous f) (a : A) (x : X)
    (ha : ∀ i, f i a = x) :
    ∃ g : C(A, X), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      TendstoUniformly (fun k ↦ f (φ k)) g atTop := by
  classical
  obtain ⟨K, hK, hfK⟩ := exists_compact_range_of_anchored f hf a x ha
  let F : ℕ → A →ᵇ X := fun k ↦
    BoundedContinuousFunction.mkOfCompact ⟨f k, hf.continuous k⟩
  have hF : Equicontinuous (fun g : Set.range F ↦ (g.1 : A → X)) := by
    have h := hf.comp (fun g : Set.range F ↦ Classical.choose g.2)
    convert h using 1
    funext g t
    have hg := congrArg (fun q : A →ᵇ X ↦ q t) (Classical.choose_spec g.2)
    exact hg.symm
  have hcompact := BoundedContinuousFunction.arzela_ascoli K hK (Set.range F)
    (by rintro _ t ⟨k, rfl⟩; exact hfK k t) hF
  obtain ⟨g, _, φ, hφ, hlim⟩ := hcompact.tendsto_subseq
    (fun k ↦ subset_closure (Set.mem_range_self k))
  exact ⟨g.toContinuousMap, φ, hφ,
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hlim⟩

end PoincareConjecture.M08
