import PoincareConjecture.Proofs.M47.TerminalCurvaturePartialInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalCurvature_exists_original_partial_charts
    {ι : Type u} {X : Type v} [TopologicalSpace X] [ChartedSpace E X]
    [IsManifold (𝓡 3) ∞ X]
    (U : ι → Set E) (hU : ∀ i, IsOpen (U i)) (f : ι → E → X)
    (hembed : ∀ i, Topology.IsOpenEmbedding (fun x : U i => f i x))
    (hsmooth : ∀ i, IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ (f i) (U i)) :
    ∃ c : ι → PartialDiffeomorph (𝓡 3) (𝓡 3) X E ∞,
      ∀ i, ((c i).symm : E → X) = f i ∧
        (c i).source = f i '' U i ∧ (c i).target = U i := by
  choose phi hphi hsource htarget using fun i =>
    terminalCurvature_exists_actual_partial_inverse (hU i) (hembed i) (hsmooth i)
  refine ⟨fun i => (phi i).symm, fun i => ?_⟩
  exact ⟨hphi i, htarget i, hsource i⟩

end PoincareConjecture.M47
