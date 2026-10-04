import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Polyhedra.FinitePolyhedralIdentityExtension
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.BoundedRegionBallInterior
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Handles.HamiltonPLAtlasNeighborhood

/-!
# Original-dimensional PL ball maps extended to the ambient space

The marked boundary is the actual ambient frontier. The checked finite
polyhedral identity extension therefore gives the same map on every
finite carrier, including all frontier points. See PrimeReduction023
sections2--3 and Hudson pp.15--19.
-/

set_option autoImplicit false

open Set Geometry

namespace Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- Extend a whole boundary-fixed finite PL ball map to the same
ambient space, with every finite carrier and both groupoid directions
certified. See PrimeReduction023 sections2--3. -/
theorem IsFinitePLBallPair.exists_supported_ambient_extension
    {C bd : Set E} (hC : IsFinitePLBallPair F C bd)
    (hdim : Module.finrank ℝ F = Module.finrank ℝ E)
    (e : C ≃ₜ C) (he : e.IsFinitePL)
    (hfix : ∀ x : C, (x : E) ∈ bd → e x = x) :
    ∃ G : E ≃ₜ E,
      (∀ x : C, G x = (e x : E)) ∧
      (∀ x ∉ interior C, G x = x) ∧
      (∀ (K : SimplicialComplex ℝ E), K.faces.Finite →
        FinitePiecewiseAffineOn (G : E → E) K.space) ∧
      G.toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E := by
  have hfront : frontier C = bd := hC.frontier_eq_of_finrank_eq hdim
  have hclosed := hC.isCompact.isClosed
  have hfrontfix : ∀ x : C, (x : E) ∈ frontier C → e x = x := by
    intro x hx
    exact hfix x (hfront ▸ hx)
  let G := e.closedExtension hclosed hfrontfix
  have hfinite (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) :
      FinitePiecewiseAffineOn (G : E → E) K.space :=
    he.closedExtension_finite_on_polyhedron hclosed hfrontfix K hK
  refine ⟨G, ?_, ?_, hfinite, ?_⟩
  · intro x
    exact e.closedExtension_apply_mem hclosed hfrontfix x.property
  · intro x hx
    exact e.closedExtension_apply_notMem_interior hclosed hfrontfix hx
  · apply G.toOpenPartialHomeomorph.mem_piecewiseAffineGroupoid_of_local_finitePL
    intro x _
    obtain ⟨K, hK, hxK, _⟩ :=
      SimplicialComplex.exists_finite_neighborhood_subset_normed
        isCompact_singleton isOpen_univ (singleton_subset_iff.mpr (mem_univ x))
    exact ⟨K.space, hxK (mem_singleton x), hfinite K hK⟩

end Set
