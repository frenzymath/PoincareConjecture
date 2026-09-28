import PoincareConjecture.Definitions.M59LoopIdentification
import Mathlib.Topology.Maps.Proper.Basic









set_option autoImplicit false

open Topology
open scoped Topology unitInterval

noncomputable section

namespace PoincareConjecture.M59SphereQuotient

variable (q : M59SphereQuotient) {X : Type*} [TopologicalSpace X] {x : X}



theorem isQuotientMap : IsQuotientMap q.map :=
  IsQuotientMap.of_surjective_continuous q.surjective q.map.continuous



theorem factorsThrough_genLoop (g : GenLoop (Fin 2) X x) :
    Function.FactorsThrough g.val q.map := by
  intro v w h
  rcases (q.exact_fibers v w).mp h with rfl | ⟨hv, hw⟩
  · rfl
  · exact (g.property v hv).trans (g.property w hw).symm



def descend (g : GenLoop (Fin 2) X x) : C(LoopTwoSphere, X) :=
  q.isQuotientMap.lift g.val (q.factorsThrough_genLoop g)



theorem descend_map (g : GenLoop (Fin 2) X x) (z : Fin 2 → I) :
    q.descend g (q.map z) = g z :=
  ContinuousMap.congr_fun (q.isQuotientMap.lift_comp g.val (q.factorsThrough_genLoop g)) z



theorem descend_pole (g : GenLoop (Fin 2) X x) : q.descend g q.pole = x := by
  have hzero : (fun _ : Fin 2 => (0 : I)) ∈ Cube.boundary (Fin 2) := ⟨0, Or.inl rfl⟩
  exact (congrArg (q.descend g) (q.boundary_collapsed _ hzero).symm).trans
    ((q.descend_map g _).trans (g.property _ hzero))

end PoincareConjecture.M59SphereQuotient
