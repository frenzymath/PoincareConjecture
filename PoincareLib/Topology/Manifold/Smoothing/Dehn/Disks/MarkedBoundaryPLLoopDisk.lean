import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.Mathlib.SquareRimLoop
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonGeometricInputs

/-!
# The concrete output of the fixed marked-boundary PL loop theorem

This record retains one actual map, its entire marked rim, properness
against the whole original boundary and explicit basepoint transport.
It supplies no existence theorem. See Dehn derivation 020 and Hatcher,
Notes on Basic 3-Manifold Topology, pp. 45--48.
-/

set_option autoImplicit false

universe u v

open Set Metric Geometry

namespace PoincareMT.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- The actual output data, with the full frontier equation and one
transported rim class outside the original subgroup. This is never
an input supplier to the loop theorem. See Dehn derivation 020. -/
structure MarkedBoundaryPLLoopDisk
    (e : ι → OpenPartialHomeomorph X V3) (R F : Set X)
    (base : F) (J : Subgroup (FundamentalGroup F base)) where
  map : V2 → X
  rim : C(Q, F)
  piecewiseAffine : PolyhedralPLInCharts e map D
  embedding : Topology.IsEmbedding (fun x : D => map x.val)
  inside : MapsTo map D R
  boundary_values : ∀ x : Q, map x.val = (rim x : X)
  whole_boundary_iff : ∀ x : D, map x.val ∈ frontier R ↔ x.val ∈ Q
  basepath : Path base (rim squareRimBase)
  outside : FundamentalGroup.fromPath
    (Path.Homotopic.Quotient.mk
      ((basepath.trans (squareRimLoop.map rim.continuous)).trans basepath.symm)) ∉ J

end PoincareMT.M76.Dehn
