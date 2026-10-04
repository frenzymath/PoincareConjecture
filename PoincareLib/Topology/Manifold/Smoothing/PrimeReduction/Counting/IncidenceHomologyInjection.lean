import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Counting.CutGraphEdgeCocycles
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Counting.CocycleHomologyEvaluation

/-!
# Incidence cycles inject into the singular homology of the cut graph

The constructed double covers detect every original edge coordinate.
-/

set_option autoImplicit false

open CategoryTheory
open scoped BigOperators

universe u

namespace PoincareMT.M76.CutGraph

variable {V I : Type u} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

noncomputable def complexVertex (ends : I → Bool → V) (v : V) :=
  realizationHomeomorph ends ⟨vertex v, vertex_mem_carrier ends v⟩

noncomputable def incidenceHomologyClass (ends : I → Bool → V)
    (R : ModuleCat.{u} (ZMod 2)) :=
  singularCycleClass R (TopCat.of (abstractComplex ends).barycentricSpace)
    ends (complexVertex ends) (complexEdgePath ends)

theorem incidenceHomologyClass_evaluation (ends : I → Bool → V)
    (R : ModuleCat.{u} (ZMod 2)) (w : I → ZMod 2)
    (z : LinearMap.ker (incidenceBoundary (K := ZMod 2) ends)) :
    incidenceHomologyClass ends R z ≫ (weightedCocycle ends w).homologyEvaluation R =
      (∑ i, z.val i * w i) • 𝟙 R := by
  calc
    _ = (∑ i, z.val i * (weightedCocycle ends w).pathValue (complexEdgePath ends i)) •
        𝟙 R := (weightedCocycle ends w).singularCycleClass_evaluation R ends
          (complexVertex ends) (complexEdgePath ends) z
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [weightedCocycle_pathValue_edge]

theorem incidenceHomologyClass_injective (ends : I → Bool → V) :
    Function.Injective (incidenceHomologyClass ends
      (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))) := by
  intro z z' h
  apply Subtype.ext
  funext i
  let R := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))
  have he := congrArg
    (fun f => f ≫ (weightedCocycle ends (Pi.single i 1)).homologyEvaluation R) h
  rw [incidenceHomologyClass_evaluation, incidenceHomologyClass_evaluation] at he
  simp [Pi.single_apply] at he
  have hv := congrArg (fun f : R ⟶ R => (f (ULift.up 1)).down) he
  change z.val i * 1 = z'.val i * 1 at hv
  simpa using hv

/-- A cycle determines an element of actual singular homology by applying
its coefficient morphism to the unit of the scalar module. -/
noncomputable def incidenceHomologyElement (ends : I → Bool → V) :
    LinearMap.ker (incidenceBoundary (K := ZMod 2) ends) →ₗ[ZMod 2]
      ↑((TopCat.toSSet.obj (TopCat.of (abstractComplex ends).barycentricSpace)).homology
        (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) 1) where
  toFun z := incidenceHomologyClass ends _ z (ULift.up 1)
  map_add' x y := by
    rw [map_add]
    rfl
  map_smul' a z := by
    rw [map_smul]
    rfl

theorem incidenceHomologyElement_injective (ends : I → Bool → V) :
    Function.Injective (incidenceHomologyElement ends) := by
  intro z z' h
  apply incidenceHomologyClass_injective ends
  ext x
  have hx : x = x.down • (ULift.up 1 : ULift.{u} (ZMod 2)) := by
    ext
    simp
  rw [hx, map_smul, map_smul]
  exact congrArg (x.down • ·) h

end PoincareMT.M76.CutGraph
