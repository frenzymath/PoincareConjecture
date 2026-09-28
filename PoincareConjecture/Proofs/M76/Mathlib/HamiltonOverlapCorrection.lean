import PoincareConjecture.Proofs.M76.Mathlib.HamiltonPLSupportedInsertion

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

variable {M E ι : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

structure SupportedPLOverlapCorrection
    (c : ι → OpenPartialHomeomorph M E) (d : OpenPartialHomeomorph M E)
    (Q : Set M) where

  neighborhood : Set M

  neighborhood_open : IsOpen neighborhood

  core_subset : Q ⊆ neighborhood

  neighborhood_subset : neighborhood ⊆ (⋃ i, (c i).source) ∩ d.source

  support : Set M

  support_compact : IsCompact support

  support_subset : support ⊆ (⋃ i, (c i).source) ∩ d.source

  correction : ((⋃ i, (c i).source) ∩ d.source : Set M) ≃ₜ
    ((⋃ i, (c i).source) ∩ d.source : Set M)

  fixed : ∀ x : ((⋃ i, (c i).source) ∩ d.source : Set M),
    (x : M) ∉ support → correction x = x

  coordinates : M → E

  coordinates_eq : ∀ x : ((⋃ i, (c i).source) ∩ d.source : Set M),
    coordinates x = d (correction x)

  locallyPL : ∀ i, LocallyPiecewiseAffineOn (coordinates ∘ (c i).symm)
    ((c i).target ∩ (c i).symm ⁻¹' neighborhood)

variable [FiniteDimensional ℝ E]

def HasSupportedPLOverlapStraightening : Prop :=
  ∀ s : Finset (OpenPartialHomeomorph M E),
    (∀ i j : s, (i : OpenPartialHomeomorph M E).symm.trans
      (j : OpenPartialHomeomorph M E) ∈ piecewiseAffineGroupoid E) →
    ∀ (d : OpenPartialHomeomorph M E) (Q : Set M), IsCompact Q →
      Q ⊆ (⋃ i : s, (i : OpenPartialHomeomorph M E).source) ∩ d.source →
      Nonempty (SupportedPLOverlapCorrection (fun i : s => (i : OpenPartialHomeomorph M E))
        d Q)

end OpenPartialHomeomorph
