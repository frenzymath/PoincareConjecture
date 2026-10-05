import PoincareLib.Topology.Manifold.Smoothing.Dehn.Isotopy.Mathlib.PLCarrierMotionRegularity
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Affine.LocallyPiecewiseAffineInverse

/-!
# Whole local PL regularity of every actual motion slice

Finite formulas on every finite polyhedron supply an actual finite
neighborhood at each ambient point. The proved inverse criterion puts
the entire homeomorphism in the original PL groupoid. See Hudson1969,
Lemma4.6, pp.97--99, and Dehn031, section3.
-/

set_option autoImplicit false

open Set unitInterval

namespace Geometry.PLCarrierMotion

/-- Every slice of the constructed motion belongs to the PL groupoid
on the whole coordinate space. The finite neighborhood is constructed
at each point, including points of the support frontier.
See Dehn031, section3. -/
theorem slice_mem_piecewiseAffineGroupoid {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {C P : Set E} {ε : ℝ} (H : PLCarrierMotion C P ε) (t : I) :
    (H.map t).toOpenPartialHomeomorph ∈ piecewiseAffineGroupoid E := by
  apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
  intro x _
  obtain ⟨K, hK, hxK, _⟩ :=
    SimplicialComplex.exists_finite_neighborhood_subset_normed
      (E := E) isCompact_singleton isOpen_univ (subset_univ {x})
  obtain ⟨L, hL, hLs, hLaff⟩ :=
    (H.finitePiecewiseAffineOn_finite_polyhedron t K hK).1
  refine ⟨L, hL, ?_, subset_univ _, hLaff⟩
  rw [hLs]
  exact hxK (mem_singleton x)

end Geometry.PLCarrierMotion
