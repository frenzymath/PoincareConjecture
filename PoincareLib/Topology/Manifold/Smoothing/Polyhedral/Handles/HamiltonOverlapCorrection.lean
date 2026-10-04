import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Handles.HamiltonPLSupportedInsertion

/-!
# Actual local data for Hamilton's overlap straightening

Retain the supported overlap homeomorphism and its local
coordinate formulas near a prescribed compact core. These
data are the geometric input of the finite atlas induction.
See Hamilton 1976, Theorems 1 and 2.1, pp. 64--69 and
M76 derivation 258.
-/

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

variable {M E ι : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual supported map and local finite PL formulas
produced by overlap straightening near a prescribed core.
The record does not assert existence of a global atlas or
of any local correction. See Hamilton p. 69 and derivation 258. -/
structure SupportedPLOverlapCorrection
    (c : ι → OpenPartialHomeomorph M E) (d : OpenPartialHomeomorph M E)
    (Q : Set M) where
  /-- Open neighborhood on which the coordinate change is PL. -/
  neighborhood : Set M
  /-- The neighborhood is open in the original topology. -/
  neighborhood_open : IsOpen neighborhood
  /-- The prescribed compact core is contained in this neighborhood. -/
  core_subset : Q ⊆ neighborhood
  /-- Only points of the genuine chart overlap are straightened. -/
  neighborhood_subset : neighborhood ⊆ (⋃ i, (c i).source) ∩ d.source
  /-- A compact carrier containing the moved points. -/
  support : Set M
  /-- Compact support allows extension through the overlap boundary. -/
  support_compact : IsCompact support
  /-- The whole support stays in the actual overlap. -/
  support_subset : support ⊆ (⋃ i, (c i).source) ∩ d.source
  /-- The actual overlap self-homeomorphism. -/
  correction : ((⋃ i, (c i).source) ∩ d.source : Set M) ≃ₜ
    ((⋃ i, (c i).source) ∩ d.source : Set M)
  /-- The correction fixes every overlap point outside the support. -/
  fixed : ∀ x : ((⋃ i, (c i).source) ∩ d.source : Set M),
    (x : M) ∉ support → correction x = x
  /-- Total coordinate expression whose values matter only on the overlap. -/
  coordinates : M → E
  /-- On the overlap these are exactly the corrected incoming coordinates. -/
  coordinates_eq : ∀ x : ((⋃ i, (c i).source) ∩ d.source : Set M),
    coordinates x = d (correction x)
  /-- Each old chart sees the actual correction as locally PL near the core. -/
  locallyPL : ∀ i, LocallyPiecewiseAffineOn (coordinates ∘ (c i).symm)
    ((c i).target ∩ (c i).symm ⁻¹' neighborhood)

variable [FiniteDimensional ℝ E]

/-- The local geometric supplier required by Hamilton's
finite atlas induction. It straightens a prescribed compact
part of one genuine overlap with a finite compatible family.
It does not assume existence of an atlas covering the manifold.
See Hamilton p. 69 and M76 derivation 258. -/
def HasSupportedPLOverlapStraightening : Prop :=
  ∀ s : Finset (OpenPartialHomeomorph M E),
    (∀ i j : s, (i : OpenPartialHomeomorph M E).symm.trans
      (j : OpenPartialHomeomorph M E) ∈ piecewiseAffineGroupoid E) →
    ∀ (d : OpenPartialHomeomorph M E) (Q : Set M), IsCompact Q →
      Q ⊆ (⋃ i : s, (i : OpenPartialHomeomorph M E).source) ∩ d.source →
      Nonempty (SupportedPLOverlapCorrection (fun i : s => (i : OpenPartialHomeomorph M E))
        d Q)

end OpenPartialHomeomorph
