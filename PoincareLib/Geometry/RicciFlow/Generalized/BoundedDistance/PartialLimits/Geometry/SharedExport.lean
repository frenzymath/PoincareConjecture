import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.PartialLimits.Cylinders.FlowConvergence

/-!
# Shared partial-limit export

The spatial embeddings, mixed within-jet convergence and the common backward
window are one output of the selected partial-limit theorem. This record is
the producer-side object consumed by both the parabolic application and neck
transfer; it contains no target neck or cap conclusion.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M28

/-- The actual partial-limit output on one fixed normalized time window.
The interval in the type of `F` is the common window, while `limit` carries
the compact-stage embeddings and all mixed within-jet convergence. Source:
Morgan--Tian Theorem 5.6 and Proposition 5.14, pp. 85-91. -/
structure PartialLimitWindowExport
    {n : ℕ} {M : ℕ → Type u}
    [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {tau : ℝ}
    (F : ∀ k, RicciFlow n (M k) (Icc (-tau) 0))
    (p : ∀ k, M k) (A : ℝ) where
  tau_pos : 0 < tau
  limit : PartialPointedFlowConvergence F p A 0

/-- The stage embedding exported by a shared partial limit. -/
def PartialLimitWindowExport.embedding
    {n : ℕ} {M : ℕ → Type u}
    [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {tau : ℝ}
    {F : ∀ k, RicciFlow n (M k) (Icc (-tau) 0)}
    {p : ∀ k, M k} {A : ℝ}
    (E : PartialLimitWindowExport F p A) :
    ∀ k, E.limit.limitCarrier.carrier → M (E.limit.subsequence k) :=
  E.limit.embedding

end PoincareMT.M28
