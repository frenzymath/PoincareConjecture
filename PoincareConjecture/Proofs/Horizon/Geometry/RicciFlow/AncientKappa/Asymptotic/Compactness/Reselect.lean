import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Subsequence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.SourceBalls







set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.PointedGeometricConvergence

def reselect {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}
    (G : PointedGeometricConvergence S) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    PointedGeometricConvergence S where
  limitCarrier := G.limitCarrier
  limitFlow := G.limitFlow
  subsequence := G.subsequence ∘ φ
  subsequence_strictMono := G.subsequence_strictMono.comp hφ
  exhaustion := G.exhaustion ∘ φ
  exhaustion_open k := G.exhaustion_open (φ k)
  exhaustion_connected k := G.exhaustion_connected (φ k)
  exhaustion_compactClosure k := G.exhaustion_compactClosure (φ k)
  exhaustion_increasing k := G.exhaustion_monotone (hφ.monotone (Nat.le_succ k))
  exhaustion_covers := by
    apply Subset.antisymm (subset_univ _)
    intro x _
    obtain ⟨j, hj⟩ := mem_iUnion.mp (show x ∈ ⋃ j, G.exhaustion j by
      rw [G.exhaustion_covers]; exact mem_univ x)
    exact mem_iUnion.mpr ⟨j, G.exhaustion_monotone (hφ.id_le j) hj⟩
  embedding := fun k ↦ G.embedding (φ k)
  base_in_exhaustion k := G.base_in_exhaustion (φ k)
  base_preserving k := G.base_preserving (φ k)
  pullback_metric_converges := by
    intro j K I hK hKj hI hIt ε hε
    obtain ⟨N, _, hN⟩ := G.pullback_metric_converges (φ j) K I hK hKj hI hIt ε hε
    refine ⟨max j N, le_max_left _ _, ?_⟩
    intro k hk t ht x hx v w hv hw
    exact hN (φ k) ((le_max_right j N).trans (hk.trans (hφ.id_le k))) t ht x hx v w hv hw
  pullback_metric_CInfinity := by
    intro q j r K hK hKj ε hε
    obtain ⟨N, _, hN⟩ := G.pullback_metric_CInfinity q (φ j) r K hK hKj ε hε
    refine ⟨max j N, le_max_left _ _, ?_⟩
    intro k hk i l z hz
    exact hN (φ k) ((le_max_right j N).trans (hk.trans (hφ.id_le k))) i l z hz

end PoincareConjecture.PointedGeometricConvergence

namespace PoincareConjecture.PointedRicciFlowCompactnessConclusion

def reselect {n : ℕ} {a b : ℝ} {H : PointedRicciFlowCompactnessHypotheses n a b}
    (G : PointedRicciFlowCompactnessConclusion H) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    PointedRicciFlowCompactnessConclusion H where
  geometric_limit := G.geometric_limit.reselect φ hφ
  complete_interior := G.complete_interior

end PoincareConjecture.PointedRicciFlowCompactnessConclusion
