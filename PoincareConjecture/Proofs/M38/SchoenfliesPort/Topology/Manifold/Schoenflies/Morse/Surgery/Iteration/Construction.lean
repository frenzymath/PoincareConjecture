import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.CapPreservation







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.PoincareConjecture

namespace M38Schoenflies



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1




theorem exists_sphereSurgeryTree_with_protected_heights
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (A : Finset Real)
    (hregular : ∀ c ∈ A, ∀ p, inner Real v (f p) = c ->
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) p ≠ 0)
    (B : Set Real) (hB : B.Finite) (hdisj : Disjoint (A : Set Real) B) :
    ∃ tree : SphereSurgeryTree v A f, tree.Protects B := by
  obtain ⟨tree, hprotected, _⟩ :=
    exists_sphereSurgeryTree_preserving_caps hf hv A hregular B hB.isCompact hdisj
  exact ⟨tree, hprotected⟩

theorem nonempty_sphereSurgeryTree_of_regular_cuts
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    {v : E3} (hv : ‖v‖ = 1) (A : Finset Real)
    (hregular : ∀ c ∈ A, ∀ p, inner Real v (f p) = c ->
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun q => inner Real v (f q)) p ≠ 0) :
    Nonempty (SphereSurgeryTree v A f) := by
  obtain ⟨tree, _⟩ := exists_sphereSurgeryTree_with_protected_heights hf hv A hregular
    ∅ finite_empty (by simp)
  exact ⟨tree⟩

end Poincare.Manifold.Schoenflies

end

end M38Schoenflies
