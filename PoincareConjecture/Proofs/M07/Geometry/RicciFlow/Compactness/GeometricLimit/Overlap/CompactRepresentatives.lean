import PoincareConjecture.Proofs.M07.Topology.Gluing.Basic
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.UniformDistance
import Mathlib.Topology.Compactness.LocallyCompact

set_option autoImplicit false
open Set Filter
open scoped Topology

namespace PoincareConjecture.ChartDistance

variable {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]

theorem exists_finite_compact_representatives
    [∀ i, WeaklyLocallyCompactSpace (X i)] (O : Poincare.Gluing.OverlapSystem X)
    {Q : Set (Quotient O.setoid)} (hQ : IsCompact Q) (hQc : IsClosed Q) :
    ∃ s : Finset (Σ i, X i), ∃ K : ∀ a : Σ i, X i, Set (X a.1),
      (∀ a ∈ s, IsCompact (K a)) ∧ (⋃ a ∈ s, O.include a.1 '' K a) = Q := by
  classical
  choose K hK hKn using fun a : Σ i, X i => exists_compact_mem_nhds a.2
  let V := fun a : Σ i, X i => O.include a.1 '' interior (K a)
  have hVo (a) : IsOpen (V a) := O.include_isOpenMap a.1 _ isOpen_interior
  have hcover : Q ⊆ ⋃ a, V a := by
    intro q _
    induction q using Quotient.inductionOn with
    | h a =>
      exact mem_iUnion.mpr ⟨a, mem_image_of_mem _ (mem_interior_iff_mem_nhds.mpr (hKn a))⟩
  obtain ⟨s, hs⟩ := hQ.elim_finite_subcover V hVo hcover
  refine ⟨s, fun a => K a ∩ O.include a.1 ⁻¹' Q, ?_, ?_⟩
  · intro a _
    exact (hK a).inter_right (hQc.preimage (O.include_isOpenEmbedding a.1).continuous)
  · apply Subset.antisymm
    · intro q hq
      obtain ⟨a, _, x, hx, rfl⟩ := by
        simpa only [mem_iUnion, exists_prop, mem_image] using hq
      exact hx.2
    · intro q hq
      obtain ⟨a, ha, x, hx, rfl⟩ := by
        simpa only [mem_iUnion, exists_prop, mem_image, V] using hs hq
      exact mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨ha, x, ⟨interior_subset hx, hq⟩, rfl⟩⟩

variable {M : ℕ → Type*} [∀ k, PseudoMetricSpace (M k)]
    {e : ∀ k i, X i → M k} {D : ∀ i j, X i × X j → ℝ}
    (hD : ∀ i j, TendstoLocallyUniformly
      (fun k (p : X i × X j) => dist (e k i p.1) (e k j p.2)) (D i j) atTop)

include hD

theorem eventually_base_dist_sub_limit_lt_on_representatives
    {i₀ : ι} (p : X i₀) (s : Finset (Σ i, X i))
    (K : ∀ a : Σ i, X i, Set (X a.1)) (hK : ∀ a ∈ s, IsCompact (K a))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ a ∈ s, ∀ x ∈ K a,
      |dist (e k i₀ p) (e k a.1 x) - D i₀ a.1 (p, x)| < ε := by
  have h := fun a ha => eventually_dist_sub_limit_lt_on_compact hD
    ({p} ×ˢ K a) (isCompact_singleton.prod (hK a ha)) hε
  filter_upwards [s.eventually_all.mpr h] with k hk a ha x hx
  exact hk a ha (p, x) ⟨mem_singleton p, hx⟩

end PoincareConjecture.ChartDistance
