import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquareRimLoop
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs










set_option autoImplicit false

universe u v

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

variable {X : Type u} [TopologicalSpace X] {ι : Type v}




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

end PoincareConjecture.M76.Dehn
