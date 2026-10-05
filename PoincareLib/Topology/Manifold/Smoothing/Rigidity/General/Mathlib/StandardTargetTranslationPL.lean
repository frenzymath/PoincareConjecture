import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.FinitePLArithmetic
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonStandardQuotientPL

/-!
# Finite PL translation in the standard target atlas

A finite PL affine lift may be translated by a finite PL scalar through
any fixed continuous-linear target direction. The source subdivision is
retained, and the standard quotient projection then gives the chartwise
PL certificate used by the relative fiberwise adjustment. See rigidity056,
section 5.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

variable (ι κ : Type*) [Fintype ι] [Fintype κ]
  (L : Submodule ℤ (κ → ℝ))

local notation "V" => ((ι ⊕ κ) → ℝ)
local notation "pi" => latticeCoordinateProjection ι κ L

variable {ι κ L} {β : Type*}

/-- A finite PL lift plus a scalar translation remains chartwise PL after
the standard lattice quotient projection. The affine lift and the target
direction are supplied locally; no global lift or chart selection is
asserted. See rigidity056, section 5. -/
theorem StandardLatticeHandleAtlas.polyhedralPL_projection_add_linear
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W]
    {d : β → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ)}
    (hd : StandardLatticeHandleAtlas ι κ L d)
    {v : W → V} {w : W → ℝ} {S : Set W}
    (hv : FinitePiecewiseAffineOn v S)
    (hw : FinitePiecewiseAffineOn w S)
    (n : ℝ →L[ℝ] V) :
    PolyhedralPLInCharts d (pi ∘ fun x => v x + n (w x)) S := by
  have hn : FinitePiecewiseAffineOn (fun x => n (w x)) S := by
    simpa [Function.comp_def] using
      hw.postcomp n.toContinuousAffineMap
  exact hd.polyhedralPL_projection (hv.add hn)

end PoincareMT.M76
