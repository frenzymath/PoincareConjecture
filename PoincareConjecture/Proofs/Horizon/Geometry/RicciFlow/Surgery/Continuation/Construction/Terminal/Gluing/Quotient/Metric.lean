import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Quotient.Carrier

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.Surgery.Terminal.Gluing

variable {ι : Type u} [Countable ι] {P : ι → Type v}
  [∀ i, TopologicalSpace (P i)]
  [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (P i)]
  [∀ i, IsManifold (𝓡 3) ∞ (P i)]
  [∀ i, SecondCountableTopology (P i)]
  (O : Poincare.Gluing.OverlapSystem P)
  (hs : ∀ i j, ContMDiffOn (𝓡 3) (𝓡 3) ∞
    (O.transition i j) (O.transition i j).source)
  (hc : ∀ i j, IsClosed {q : P i × P j | O.Rel ⟨i, q.1⟩ ⟨j, q.2⟩})
  (g : ∀ i, RiemannianMetric 3 (P i))
  (hg : ∀ i j (x : P i), x ∈ (O.transition i j).source →
    ∀ a b : TangentSpace (𝓡 3) x,
      (g i).inner x a b = (g j).inner (O.transition i j x)
        (mfderiv (𝓡 3) (𝓡 3) (O.transition i j) x a)
        (mfderiv (𝓡 3) (𝓡 3) (O.transition i j) x b))

def metric : RiemannianMetric 3 (carrier O hs hc).carrier := by
  letI := chartedSpace O
  letI := isManifold O hs
  exact Classical.choose (O.exists_unique_metric_of_transition_invariance g
    (carrier_include_isLocalDiffeomorph O hs hc) hs hg)

theorem metric_preserves (i : ι) (x : P i) (a b : TangentSpace (𝓡 3) x) :
    letI := chartedSpace O
    (g i).inner x a b = (metric O hs hc g hg).inner (O.include i x)
      (mfderiv (𝓡 3) (𝓡 3) (O.include i) x a)
      (mfderiv (𝓡 3) (𝓡 3) (O.include i) x b) := by
  let := chartedSpace O
  let := isManifold O hs
  exact (Classical.choose_spec (O.exists_unique_metric_of_transition_invariance g
    (carrier_include_isLocalDiffeomorph O hs hc) hs hg)).1 i x a b

end PoincareConjecture.Surgery.Terminal.Gluing
