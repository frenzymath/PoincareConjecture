import PoincareConjecture.Proofs.M59.Sec18_3_LoopSpace.PairHomotopy
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology unitInterval

universe u v

namespace PoincareConjecture

variable {M : Type u} [MetricSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem m59_exists_uniform_loop_homotopy_radius
    (hcompact : IsCompact (univ : Set M)) :
    ∃ epsilon > 0,
      ∀ {X : Type v} [TopologicalSpace X] (F G : C(X, C1FreeLoopSpace (M := M))),
        (∀ x z, dist (G x z) (F x z) < epsilon) →
        ∃ H : F.Homotopy G, ∀ t x p,
          F x = constantC1Loop p → G x = constantC1Loop p → H (t, x) = constantC1Loop p := by
  let : CompactSpace M := isCompact_univ_iff.mp hcompact
  obtain ⟨U, hU, hdiag, hhom⟩ := m59_exists_near_loop_homotopy.{u, v} hcompact
  obtain ⟨epsilon, he, hnear⟩ := isCompact_diagonal.exists_thickening_subset_open hU hdiag
  refine ⟨epsilon, he, ?_⟩
  intro X _ F G hFG
  apply hhom F G
  intro x z
  apply hnear
  apply Metric.mem_thickening_iff.mpr
  refine ⟨(F x z, F x z), rfl, ?_⟩
  simpa only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)] using hFG x z

end PoincareConjecture
