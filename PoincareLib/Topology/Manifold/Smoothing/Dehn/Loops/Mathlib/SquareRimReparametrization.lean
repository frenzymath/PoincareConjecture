import PoincareLib.Topology.Manifold.Smoothing.Dehn.Loops.Mathlib.CircleRimReparametrization
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.MarkedBoundaryPLLoopDisk
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Handles.HamiltonIndexOneSquareCircle

/-!
# Normal-subgroup invariance of the entire marked square rim

An actual square-rim homeomorphism can change orientation and initial point.
The full reparametrized loop retains membership, or exclusion, in every
normal subgroup, with arbitrary actual basepoint paths.
-/

noncomputable section
set_option autoImplicit false

open Set Metric Geometry

namespace PoincareMT.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1

/-- The existing perimeter homeomorphism identifies the square rim with
the standard unit circle. No traversal or winding certificate is assumed. -/
def squareRimUnitCircle : Q ≃ₜ UnitCircle :=
  HamiltonIndexOne.squareCircle.symm.trans
    ((AddCircle.homeomorphCircle (by norm_num : 4 * (2 : ℝ) ≠ 0)).trans
      complexCircleDiffeomorph.toHomeomorph)

variable {X : Type*} [TopologicalSpace X]

/-- Reparametrizing the actual full square rim by a homeomorphism preserves
the original normal-subgroup test, including arbitrary endpoint whiskers. -/
theorem squareRimLoop_homeomorph_mem_iff
    (h : Q ≃ₜ Q) (f : C(Q, X)) {b : X}
    (J : Subgroup (FundamentalGroup X b)) [J.Normal]
    (p : Path b (f squareRimBase)) (q : Path b (f (h squareRimBase))) :
    q.whiskeredLoopClass ((squareRimLoop.map h.continuous).map f.continuous) ∈ J ↔
      p.whiskeredLoopClass (squareRimLoop.map f.continuous) ∈ J :=
  circleLikeLoop_homeomorph_mem_iff squareRimUnitCircle squareRimLoop h f J p q

/-- The original excluded full rim remains excluded after an actual rim
homeomorphism, without a supplied homotopy or orientation choice. -/
theorem squareRimLoop_homeomorph_excluded
    (h : Q ≃ₜ Q) (f : C(Q, X)) {b : X}
    (J : Subgroup (FundamentalGroup X b)) [J.Normal]
    (p : Path b (f squareRimBase)) (q : Path b (f (h squareRimBase)))
    (hout : p.whiskeredLoopClass (squareRimLoop.map f.continuous) ∉ J) :
    q.whiskeredLoopClass ((squareRimLoop.map h.continuous).map f.continuous) ∉ J :=
  fun hin => hout ((squareRimLoop_homeomorph_mem_iff h f J p q).mp hin)

/-- A constructed marked disk's stored exclusion is retained by every
actual homeomorphic full-rim traversal and any actual new whisker. -/
theorem MarkedBoundaryPLLoopDisk.reparametrized_rim_excluded
    {ι : Type*} {e : ι → OpenPartialHomeomorph X V3} {R F : Set X}
    {base : F} {J : Subgroup (FundamentalGroup F base)} [J.Normal]
    (d : MarkedBoundaryPLLoopDisk e R F base J)
    (h : Q ≃ₜ Q) (q : Path base (d.rim (h squareRimBase))) :
    q.whiskeredLoopClass ((squareRimLoop.map h.continuous).map d.rim.continuous) ∉ J :=
  squareRimLoop_homeomorph_excluded h d.rim J d.basepath q d.outside

end PoincareMT.M76.Dehn
