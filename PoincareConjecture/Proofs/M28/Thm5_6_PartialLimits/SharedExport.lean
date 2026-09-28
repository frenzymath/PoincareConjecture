import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.FlowConvergence










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28





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

end PoincareConjecture.M28
