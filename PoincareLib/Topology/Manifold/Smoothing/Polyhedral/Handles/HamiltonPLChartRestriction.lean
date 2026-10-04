import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Handles.HamiltonPLAtlasNeighborhood
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Restricting the actual PL transitions during atlas insertion

Finite local formulas on the overlap give a PL coordinate
transition. Restricting either chart preserves compatibility;
restricting both into a controlled overlap uses only that local
transition. See Hamilton 1976, p. 69 and M76 derivation 258.
-/

set_option autoImplicit false

open Set Geometry

namespace OpenPartialHomeomorph

variable {M E : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A chart's self transition is locally the affine identity
on its actual source. See Hamilton p. 69 and derivation 258. -/
theorem self_transition_mem_piecewiseAffineGroupoid
    (c : OpenPartialHomeomorph M E) : c.symm.trans c ∈ piecewiseAffineGroupoid E := by
  apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
  have hid := locallyPiecewiseAffineOn_affine (ContinuousAffineMap.id ℝ E)
    (c.symm.trans c).open_source
  apply hid.congr
  intro x hx
  change x = c (c.symm x)
  exact (c.right_inv hx.1).symm

/-- Restricting both coordinate charts preserves their PL
transition, including when either restricted source is empty.
See Hamilton p. 69 and derivation 258. -/
theorem restricted_transition_mem_piecewiseAffineGroupoid
    (c d : OpenPartialHomeomorph M E)
    (hcd : c.symm.trans d ∈ piecewiseAffineGroupoid E) (U V : Set M) :
    (c.restr U).symm.trans (d.restr V) ∈ piecewiseAffineGroupoid E := by
  apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
  have hf := (mem_piecewiseAffineGroupoid_iff_forward _).mp hcd
  apply hf.mono ((c.restr U).symm.trans (d.restr V)).open_source
  intro x hx
  exact ⟨hx.1.1, hx.2.1⟩

/-- Two restricted chart domains meeting only in a controlled
open region use only the PL transition already certified on
that region. See Hamilton p. 69 and M76 derivation 258. -/
theorem restricted_transition_mem_of_overlap
    (c d : OpenPartialHomeomorph M E) {U V N : Set M}
    (hN : IsOpen N) (hUV : U ∩ V ⊆ N)
    (hcd : c.symm.trans (d.restr N) ∈ piecewiseAffineGroupoid E) :
    (c.restr U).symm.trans (d.restr V) ∈ piecewiseAffineGroupoid E := by
  apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
  have hf := (mem_piecewiseAffineGroupoid_iff_forward _).mp hcd
  apply hf.mono ((c.restr U).symm.trans (d.restr V)).open_source
  intro x hx
  refine ⟨hx.1.1, hx.2.1, ?_⟩
  rw [hN.interior_eq]
  exact hUV ⟨interior_subset hx.1.2, interior_subset hx.2.2⟩

end OpenPartialHomeomorph
