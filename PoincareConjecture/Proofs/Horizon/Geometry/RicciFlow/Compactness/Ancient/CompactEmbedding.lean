import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Pointed

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.AncientPointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.t2Space

variable {n : ℕ} {C : ℕ → FlowCarrier.{0} n}
  {g : ∀ k, ℝ → (C k).metric} {p : ∀ k, (C k).carrier} {T : ℝ}

theorem exists_exhaustion_superset
    (G : AncientPointedGeometricConvergence C g p T)
    {K : Set G.limitCarrier.carrier} (hK : IsCompact K) :
    ∃ j, K ⊆ G.exhaustion j := by
  have hmono : Monotone G.exhaustion :=
    monotone_nat_of_le_succ G.exhaustion_increasing
  exact hK.elim_directed_cover G.exhaustion G.exhaustion_open
    (by rw [G.exhaustion_covers]; exact subset_univ _) hmono.directed_le

theorem eventually_isEmbedding_comp_of_compact
    (G : AncientPointedGeometricConvergence C g p T)
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    {f : K → G.limitCarrier.carrier} (hf : Continuous f) (hinj : Function.Injective f) :
    ∀ᶠ i in atTop, Topology.IsEmbedding (G.embedding i ∘ f) := by
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (isCompact_range hf)
  have hmono : Monotone G.exhaustion :=
    monotone_nat_of_le_succ G.exhaustion_increasing
  have hfembed : Topology.IsEmbedding f := (hf.isClosedEmbedding hinj).isEmbedding
  filter_upwards [eventually_ge_atTop j] with i hji
  have hmem (x : K) : f x ∈ G.exhaustion i := hmono hji (hj (mem_range_self x))
  exact (G.embedding_open i).isEmbedding.comp
    (hfembed.codRestrict (G.exhaustion i) hmem)

end PoincareConjecture.AncientPointedGeometricConvergence
