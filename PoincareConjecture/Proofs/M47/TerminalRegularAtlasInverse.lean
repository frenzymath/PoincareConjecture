import PoincareConjecture.Proofs.M47.TerminalCurvaturePartialInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u v w

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem terminalSource_atlas_actual_inverse
    {X : Type u} {Y : Type v} {M : Type w}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace M]
    [ChartedSpace E X] [ChartedSpace E Y] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ Y] [IsManifold (𝓡 3) ∞ M]
    [Nonempty X]
    (j : PartialDiffeomorph (𝓡 3) (𝓡 3) Y M ∞) (hj : j.source = univ)
    {V : Set X} (hV : IsOpen V) (f : X → M)
    (hembed : Topology.IsOpenEmbedding (fun x : V => f x))
    (hsmooth : IsLocalDiffeomorphOn (𝓡 3) (𝓡 3) ∞ f V)
    (hcapture : MapsTo f V j.target) :
    ∃ phi : PartialDiffeomorph (𝓡 3) (𝓡 3) X Y ∞,
      (phi : X → Y) = j.symm ∘ f ∧ phi.source = V ∧
      (∀ x ∈ V, j (phi x) = f x) ∧
      ∀ p ∈ V, ∀ y0 : Y, f p = j y0 → phi p = y0 := by
  obtain ⟨q, hq, hsource, _htarget⟩ :=
    terminalCurvature_exists_actual_partial_inverse hV hembed hsmooth
  let phi := q.trans j.symm
  have hphi : (phi : X → Y) = j.symm ∘ f := by
    change j.symm ∘ (q : X → M) = j.symm ∘ f
    rw [hq]
  have hdomain : phi.source = V := by
    ext x
    change (x ∈ q.source ∧ q x ∈ j.target) ↔ x ∈ V
    rw [hsource, hq]
    exact ⟨And.left, fun hx => ⟨hx, hcapture hx⟩⟩
  refine ⟨phi, hphi, hdomain, ?_, ?_⟩
  · intro x hx
    rw [hphi]
    exact j.right_inv (hcapture hx)
  · intro p _hp y0 heq
    rw [hphi]
    change j.symm (f p) = y0
    rw [heq]
    exact j.left_inv (hj.symm ▸ mem_univ y0)

end PoincareConjecture.M47
