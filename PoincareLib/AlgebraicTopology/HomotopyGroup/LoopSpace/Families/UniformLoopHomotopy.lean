import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Families.PairHomotopy
import Mathlib.Topology.MetricSpace.Thickening

/-!
# A uniform value radius for C1 loop homotopy

Compactness converts the local diagonal neighborhood into one value-distance
bound. This bound is independent of the parameter space. Source: MT Claim
18.16, p. 430, using the local contraction of Lemma 18.27, p. 434.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology unitInterval

universe u v

namespace PoincareMT

variable {M : Type u} [MetricSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- A compact manifold has a uniform radius such that pointwise-close C1
loop families are homotopic, fixing common constant-loop parameters.
Source: MT Claim 18.16, p. 430, C1 approximation derivation. -/
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

end PoincareMT
