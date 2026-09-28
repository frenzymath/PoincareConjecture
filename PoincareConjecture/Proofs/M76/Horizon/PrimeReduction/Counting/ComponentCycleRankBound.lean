import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.CutGraphComponentHomology
import Mathlib.LinearAlgebra.Dimension.Constructions









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomologicalComplex

universe u
namespace PoincareConjecture.M76.CutGraph
open ModTwoMayerVietoris

variable {V I X Q : Type u} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
  [TopologicalSpace X] [TopologicalSpace Q]

noncomputable def componentCycleHomology (ends : I → Bool → V)
    (j : C(Q, X)) (s : C(carrier ends, X)) :
    (homology Q 1 × LinearMap.ker (incidenceBoundary (K := ZMod 2) ends)) →ₗ[ZMod 2]
      homology X 1 :=
  (homologyMapOf j 1).hom.coprod (sectionIncidenceHomology ends s)

theorem componentCycleHomology_injective (ends : I → Bool → V)
    (j : C(Q, X)) (q : C(X, carrier ends)) (s : C(carrier ends, X))
    (H : (q.comp s).Homotopic (ContinuousMap.id (carrier ends)))
    (hj : Function.Injective (homologyMapOf j 1))
    (hzero : homologyMapOf j 1 ≫ homologyMapOf q 1 = 0) :
    Function.Injective (componentCycleHomology ends j s) := by
  have hf (x : homology Q 1) : homologyMapOf q 1 (homologyMapOf j 1 x) = 0 :=
    congrArg (fun f => f x) hzero
  have hg (z : LinearMap.ker (incidenceBoundary (K := ZMod 2) ends)) :
      homologyMapOf q 1 (sectionIncidenceHomology ends s z) = carrierIncidenceHomology ends z := by
    have he := moduleHomologyMap_section_comp coefficient q s H 1
    exact congrArg (fun f => f (carrierIncidenceHomology ends z)) he
  intro x y hxy
  have h : homologyMapOf j 1 x.1 + sectionIncidenceHomology ends s x.2 =
      homologyMapOf j 1 y.1 + sectionIncidenceHomology ends s y.2 := hxy
  have hh := congrArg (homologyMapOf q 1) h
  simp only [map_add, hf, hg, zero_add] at hh
  have hz := carrierIncidenceHomology_injective ends hh
  apply Prod.ext _ hz
  rw [hz] at h
  exact hj (add_right_cancel h)

theorem component_cycle_rank_le (ends : I → Bool → V)
    (j : C(Q, X)) (q : C(X, carrier ends)) (s : C(carrier ends, X))
    (H : (q.comp s).Homotopic (ContinuousMap.id (carrier ends)))
    (hj : Function.Injective (homologyMapOf j 1))
    (hzero : homologyMapOf j 1 ≫ homologyMapOf q 1 = 0)
    [Module.Finite (ZMod 2) (homology X 1)] :
    Module.finrank (ZMod 2) (homology Q 1) +
      Module.finrank (ZMod 2) (LinearMap.ker (incidenceBoundary (K := ZMod 2) ends)) ≤
        Module.finrank (ZMod 2) (homology X 1) := by
  let : Module.Finite (ZMod 2) (homology Q 1) := Module.Finite.of_injective
    (homologyMapOf j 1).hom hj
  have h := LinearMap.finrank_le_finrank_of_injective
    (componentCycleHomology_injective ends j q s H hj hzero)
  simpa only [Module.finrank_prod] using h

end PoincareConjecture.M76.CutGraph
