import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.Identification
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Descending based cubes through the fixed sphere parameter

Exact fibers let every based square descend uniquely to a continuous sphere
map with the specified pole value. Source: MT Claim 18.16 and Definition
18.17, printed p. 430.
-/

set_option autoImplicit false

open Topology
open scoped Topology unitInterval

noncomputable section

namespace PoincareMT.M59SphereQuotient

variable (q : M59SphereQuotient) {X : Type*} [TopologicalSpace X] {x : X}

/-- The fixed parameter is a quotient map by compactness and Hausdorffness.
Source: MT Claim 18.16, printed p. 430. -/
theorem isQuotientMap : IsQuotientMap q.map :=
  IsQuotientMap.of_surjective_continuous q.surjective q.map.continuous

/-- A based cube is constant on every fiber of the exact sphere parameter.
Source: MT Claim 18.16, printed p. 430. -/
theorem factorsThrough_genLoop (g : GenLoop (Fin 2) X x) :
    Function.FactorsThrough g.val q.map := by
  intro v w h
  rcases (q.exact_fibers v w).mp h with rfl | ⟨hv, hw⟩
  · rfl
  · exact (g.property v hv).trans (g.property w hw).symm

/-- The sphere map represented by a based square using exactly q.map.
Source: MT Definition 18.17, printed p. 430. -/
def descend (g : GenLoop (Fin 2) X x) : C(LoopTwoSphere, X) :=
  q.isQuotientMap.lift g.val (q.factorsThrough_genLoop g)

/-- Descent agrees with the original representative on every cube point.
Source: MT Definition 18.17, printed p. 430. -/
theorem descend_map (g : GenLoop (Fin 2) X x) (z : Fin 2 → I) :
    q.descend g (q.map z) = g z :=
  ContinuousMap.congr_fun (q.isQuotientMap.lift_comp g.val (q.factorsThrough_genLoop g)) z

/-- Descent takes the chosen pole to the exact based value. Source:
MT Definition 18.17, printed p. 430. -/
theorem descend_pole (g : GenLoop (Fin 2) X x) : q.descend g q.pole = x := by
  have hzero : (fun _ : Fin 2 => (0 : I)) ∈ Cube.boundary (Fin 2) := ⟨0, Or.inl rfl⟩
  exact (congrArg (q.descend g) (q.boundary_collapsed _ hzero).symm).trans
    ((q.descend_map g _).trans (g.property _ hzero))

end PoincareMT.M59SphereQuotient
