import PoincareLib.Topology.Manifold.Smoothing.Rigidity.General.StandardHierarchySurfaces
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Arcs.Mathlib.PeriodCircleLoop

/-!
# Nontrivial based groups of the actual first hierarchy targets

The explicit period loop survives the actual circle sections and then
the original-coordinate surface retractions. No group classification
or source preimage theorem is assumed. See Waldhausen1968, pp.58--60,
77--79, and rigidity050, sections2--4.
-/

set_option autoImplicit false

open Set Metric

namespace PoincareMT.M76

local notation "D1" => closedBall (0 : Fin 1 → ℝ) 1
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) hamiltonZeroPeriodLattice
local notation "H1" => LatticeHandle (Fin 1) (Fin 2)
  (hamiltonLowerPeriodLattice (Fin 2))
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "C1" => AddCircle (4 * (128 : ℝ))

/-- A literal circle period survives in the first target torus at
its original origin. See rigidity050, sections2--3. -/
theorem nontrivial_pi1_hamiltonZeroHierarchyTorus :
    Nontrivial (FundamentalGroup (C0 × C0) (0, 0)) := by
  let : Fact (0 < 4 * (16 : ℝ)) := ⟨by norm_num⟩
  let : Nontrivial (FundamentalGroup C0 0) :=
    AddCircle.nontrivial_fundamentalGroup_zero (4 * (16 : ℝ))
  exact (FundamentalGroup.map_prodMk_left_injective (0 : C0) (0 : C0)).nontrivial

/-- The original closed handle has nontrivial based fundamental
group, proved from an actual loop and retraction. See050, section3. -/
theorem nontrivial_pi1_hamiltonZeroHandle :
    Nontrivial (FundamentalGroup H0 (hamiltonZeroHierarchyTorus (0, 0))) := by
  let : Nontrivial (FundamentalGroup (C0 × C0) (0, 0)) :=
    nontrivial_pi1_hamiltonZeroHierarchyTorus
  exact (hamiltonZeroHierarchyTorus_pi1_injective (0, 0)).nontrivial

/-- A literal period survives at every original interval point of
the first target annulus. See rigidity050, sections2--4. -/
theorem nontrivial_pi1_hamiltonOneHierarchyAnnulus (x : D1) :
    Nontrivial (FundamentalGroup (D1 × C1) (x, 0)) := by
  let : Fact (0 < 4 * (128 : ℝ)) := ⟨by norm_num⟩
  let : Nontrivial (FundamentalGroup C1 0) :=
    AddCircle.nontrivial_fundamentalGroup_zero (4 * (128 : ℝ))
  exact (FundamentalGroup.map_prodMk_right_injective x (0 : C1)).nontrivial

/-- The original interval-torus handle has nontrivial based group
at each retained annulus basepoint. See rigidity050, section4. -/
theorem nontrivial_pi1_hamiltonOneHandle (x : D1) :
    Nontrivial (FundamentalGroup H1 (hamiltonOneHierarchyAnnulus (x, 0))) := by
  let : Nontrivial (FundamentalGroup (D1 × C1) (x, 0)) :=
    nontrivial_pi1_hamiltonOneHierarchyAnnulus x
  exact (hamiltonOneHierarchyAnnulus_pi1_injective (x, 0)).nontrivial

end PoincareMT.M76
