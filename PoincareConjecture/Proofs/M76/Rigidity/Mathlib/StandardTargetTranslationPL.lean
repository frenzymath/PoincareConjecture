import PoincareConjecture.Proofs.M76.Mathlib.FinitePLArithmetic
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonStandardQuotientPL

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

variable (ι κ : Type*) [Fintype ι] [Fintype κ]
  (L : Submodule ℤ (κ → ℝ))

local notation "V" => ((ι ⊕ κ) → ℝ)
local notation "pi" => latticeCoordinateProjection ι κ L

variable {ι κ L} {β : Type*}

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

end PoincareConjecture.M76
