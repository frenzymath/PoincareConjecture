import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.Extraction
import PoincareConjecture.Proofs.M07.Topology.Gluing.Separation

set_option autoImplicit false
open Set Filter Metric
open scoped Topology NNReal

namespace PoincareConjecture.ChartDistance

variable {ι : Type*} {X : ι → Type*} [∀ i, MetricSpace (X i)]
    [∀ i, LocallyCompactSpace (X i)] [∀ i, Nonempty (X i)]
    {M : ℕ → Type*} [∀ k, MetricSpace (M k)]
    {e : ∀ k i, X i → M k} {D : ∀ i j, C(X i × X j, ℝ)}
    (hD : ∀ i j x y, Tendsto (fun k => dist (e k i x) (e k j y)) atTop
      (𝓝 (D i j (x, y))))
    (L : ι → ℝ≥0) (he : ∀ k i, LipschitzWith (L i) (e k i))
    (c : ι → ℝ) (hc : ∀ i, 0 < c i)
    (hlower : ∀ k i x y, c i * dist x y ≤ dist (e k i x) (e k i y))
    (hopen : ∀ k i, Topology.IsOpenEmbedding (e k i))
    (hconn : ∀ k (p : M k) r, IsPreconnected (ball p r))

noncomputable def overlapSystem : Poincare.Gluing.OverlapSystem X where
  transition := overlapHomeomorph hD L he c hc hlower hopen hconn
  self := fun i => by
    apply OpenPartialHomeomorph.ext
    · exact transition_self hD c hc hlower i
    · exact transition_self hD c hc hlower i
    · exact overlap_self hD i
  inverse := fun _ _ => rfl
  comp_source := fun _ _ _ _ hx hy => (transition_cocycle hD c hc hlower hx hy).1
  comp_apply := fun _ _ _ _ hx hy => (transition_cocycle hD c hc hlower hx hy).2

include hD in
theorem overlapSystem_rel_iff (i j : ι) (x : X i) (y : X j) :
    (overlapSystem hD L he c hc hlower hopen hconn).Rel ⟨i, x⟩ ⟨j, y⟩ ↔
      D i j (x, y) = 0 :=
  (zero_iff_transition hD c hc hlower).symm

include hD in
theorem overlapSystem_closed (i j : ι) :
    IsClosed {p : X i × X j |
      (overlapSystem hD L he c hc hlower hopen hconn).Rel ⟨i, p.1⟩ ⟨j, p.2⟩} := by
  have hset : {p : X i × X j |
      (overlapSystem hD L he c hc hlower hopen hconn).Rel ⟨i, p.1⟩ ⟨j, p.2⟩} =
      {p | D i j p = 0} := by
    ext p
    exact overlapSystem_rel_iff hD L he c hc hlower hopen hconn i j p.1 p.2
  rw [hset]
  exact isClosed_zero (D i j)

include hD in
theorem overlapSystem_quotient_t2Space :
    T2Space (Quotient (overlapSystem hD L he c hc hlower hopen hconn).setoid) :=
  (overlapSystem hD L he c hc hlower hopen hconn).quotient_t2Space
    (overlapSystem_closed hD L he c hc hlower hopen hconn)

end PoincareConjecture.ChartDistance
