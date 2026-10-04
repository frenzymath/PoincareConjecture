import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.FinitePLHomeomorph
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.UnitBallPairs

/-!
# Restricting finite PL homeomorphisms to polyhedral subsets

Exact carrier reidentification and restriction to a finite
polyhedron preserve PL regularity. See Hudson 1969, pp. 12--19
and M76 derivations 119--120.
-/

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {s s' b : Set E} {t t' c : Set F} {e : s ≃ₜ t}

/-- Reidentifying the source and target by exact set equalities
retains finite PL regularity. See M76 derivation 119. -/
theorem IsFinitePL.setCongr (he : e.IsFinitePL) (hs : s = s') (ht : t = t') :
    ((Homeomorph.setCongr hs.symm).trans (e.trans (Homeomorph.setCongr ht))).IsFinitePL := by
  obtain ⟨f, hf, he⟩ := he
  exact ⟨f, hs ▸ hf, fun x => he ⟨x, hs.symm ▸ x.property⟩⟩

/-- Restriction to an explicitly triangulated subset is finite
PL, with the ambient subspace topologies retained.
See Hudson pp. 12--19 and M76 derivation 119. -/
theorem IsFinitePL.restrictSubsets [FiniteDimensional ℝ E]
    (he : e.IsFinitePL) (hb : b ⊆ s) (hc : c ⊆ t)
    (hmem : ∀ x : s, (x : E) ∈ b ↔ (e x : F) ∈ c)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hspace : J.space = b) :
    (e.restrictSubsets hb hc hmem).IsFinitePL := by
  obtain ⟨f, hf, he⟩ := he
  refine ⟨f, ?_, fun x => he ⟨x, hb x.property⟩⟩
  rw [← hspace]
  exact hf.restrict J hJ (hspace.subset.trans hb)

end Homeomorph
