import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Basic







set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

def AncientSpacetimeEmbedding.restrict {τ : ℝ} {R : AncientRescaling K τ}
    {L : AncientLimitFlow n} {U V : Set (ℝ × L.carrier.carrier)}
    (e : AncientSpacetimeEmbedding (R := R) L V) (hUV : U ⊆ V) :
    AncientSpacetimeEmbedding (R := R) L U where
  toFun := e.toFun
  time_preserving := e.time_preserving
  injective_on := e.injective_on.mono hUV
  inverse := e.inverse
  left_inverse := fun p hp => e.left_inverse p (hUV hp)
  right_inverse := fun q hq => e.right_inverse q (image_mono hUV hq)
  smooth_on := e.smooth_on.mono hUV
  smooth_inverse_on := e.smooth_inverse_on.mono (image_mono hUV)

def AncientCompactTimeConvergence.reselect (G : AncientCompactTimeConvergence S)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) : AncientCompactTimeConvergence S where
  limit := G.limit
  subsequence := G.subsequence ∘ φ
  subsequence_strictMono := G.subsequence_strictMono.comp hφ
  exhaustion := G.exhaustion ∘ φ
  exhaustion_open k := G.exhaustion_open (φ k)
  exhaustion_connected k := G.exhaustion_connected (φ k)
  exhaustion_compactClosure k := G.exhaustion_compactClosure (φ k)
  base_in_exhaustion k := G.base_in_exhaustion (φ k)
  exhaustion_increasing k := (monotone_nat_of_le_succ G.exhaustion_increasing)
    (hφ.monotone (Nat.le_succ k))
  exhaustion_covers := by
    apply Subset.antisymm (subset_univ _)
    intro x _
    obtain ⟨j, hj⟩ := mem_iUnion.mp (show x ∈ ⋃ j, G.exhaustion j by
      rw [G.exhaustion_covers]; exact mem_univ x)
    exact mem_iUnion.mpr ⟨j,
      (monotone_nat_of_le_succ G.exhaustion_increasing) (hφ.id_le j) hj⟩
  time_window_subset := G.time_window_subset
  time_window_increasing := G.time_window_increasing
  time_window_base := G.time_window_base
  time_window_covers := G.time_window_covers
  embedding k := (G.embedding (φ k)).restrict
    (prod_mono (ancientM18TimeWindow_mono (hφ.id_le k)) Subset.rfl)
  spatial_time_independent k s t x hs ht hx := G.spatial_time_independent (φ k) s t x
    (ancientM18TimeWindow_mono (hφ.id_le k) hs)
    (ancientM18TimeWindow_mono (hφ.id_le k) ht) hx
  base_preserving k := G.base_preserving (φ k)
  pullback_metric_CInfinity := by
    intro q j r A hA hAU ε hε
    have hAφ : A ⊆ {p | p.1 ∈ ancientM18TimeWindow (φ j) ∧
        p.2 ∈ (extChartAt (𝓡 n) q).target ∧
        (extChartAt (𝓡 n) q).symm p.2 ∈ G.exhaustion (φ j)} :=
      fun p hp => ⟨ancientM18TimeWindow_mono (hφ.id_le j) (hAU hp).1, (hAU hp).2⟩
    obtain ⟨N, _, hN⟩ := G.pullback_metric_CInfinity q (φ j) r A hA hAφ ε hε
    exact ⟨max j N, le_max_left _ _, fun k hk =>
      hN (φ k) ((le_max_right _ _).trans (hk.trans (hφ.id_le k)))⟩

end PoincareConjecture
