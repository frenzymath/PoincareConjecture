import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.CircleRimReparametrization
import PoincareConjecture.Proofs.M76.Dehn.MarkedBoundaryPLLoopDisk
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneSquareCircle

noncomputable section
set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1

def squareRimUnitCircle : Q ≃ₜ UnitCircle :=
  HamiltonIndexOne.squareCircle.symm.trans
    ((AddCircle.homeomorphCircle (by norm_num : 4 * (2 : ℝ) ≠ 0)).trans
      complexCircleDiffeomorph.toHomeomorph)

variable {X : Type*} [TopologicalSpace X]

theorem squareRimLoop_homeomorph_mem_iff
    (h : Q ≃ₜ Q) (f : C(Q, X)) {b : X}
    (J : Subgroup (FundamentalGroup X b)) [J.Normal]
    (p : Path b (f squareRimBase)) (q : Path b (f (h squareRimBase))) :
    q.whiskeredLoopClass ((squareRimLoop.map h.continuous).map f.continuous) ∈ J ↔
      p.whiskeredLoopClass (squareRimLoop.map f.continuous) ∈ J :=
  circleLikeLoop_homeomorph_mem_iff squareRimUnitCircle squareRimLoop h f J p q

theorem squareRimLoop_homeomorph_excluded
    (h : Q ≃ₜ Q) (f : C(Q, X)) {b : X}
    (J : Subgroup (FundamentalGroup X b)) [J.Normal]
    (p : Path b (f squareRimBase)) (q : Path b (f (h squareRimBase)))
    (hout : p.whiskeredLoopClass (squareRimLoop.map f.continuous) ∉ J) :
    q.whiskeredLoopClass ((squareRimLoop.map h.continuous).map f.continuous) ∉ J :=
  fun hin => hout ((squareRimLoop_homeomorph_mem_iff h f J p q).mp hin)

theorem MarkedBoundaryPLLoopDisk.reparametrized_rim_excluded
    {ι : Type*} {e : ι → OpenPartialHomeomorph X V3} {R F : Set X}
    {base : F} {J : Subgroup (FundamentalGroup F base)} [J.Normal]
    (d : MarkedBoundaryPLLoopDisk e R F base J)
    (h : Q ≃ₜ Q) (q : Path base (d.rim (h squareRimBase))) :
    q.whiskeredLoopClass ((squareRimLoop.map h.continuous).map d.rim.continuous) ∉ J :=
  squareRimLoop_homeomorph_excluded h d.rim J d.basepath q d.outside

end PoincareConjecture.M76.Dehn
