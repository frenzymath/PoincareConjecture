import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.IncidenceHomologyInjection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.OriginalCutHomologyRetract

set_option autoImplicit false

open CategoryTheory

universe u

namespace PoincareConjecture.M76.CutGraph

variable {V I X : Type u} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
  [TopologicalSpace X]

noncomputable def carrierIncidenceHomology (ends : I → Bool → V) :
    LinearMap.ker (incidenceBoundary (K := ZMod 2) ends) →ₗ[ZMod 2]
      ↑((TopCat.toSSet.obj (TopCat.of (carrier ends))).homology
        (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) 1) :=
  (moduleHomologyMap (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))
    ⟨(realizationHomeomorph ends).symm, (realizationHomeomorph ends).symm.continuous⟩ 1).hom.comp
      (incidenceHomologyElement ends)

theorem carrierIncidenceHomology_injective (ends : I → Bool → V) :
    Function.Injective (carrierIncidenceHomology ends) := by
  apply Function.Injective.comp _ (incidenceHomologyElement_injective ends)
  let e := realizationHomeomorph ends
  apply moduleHomologyMap_section_injective _ ⟨e, e.continuous⟩
    ⟨e.symm, e.symm.continuous⟩
  have h : (⟨e, e.continuous⟩ : C(carrier ends, _)).comp
      ⟨e.symm, e.symm.continuous⟩ =
        ContinuousMap.id (abstractComplex ends).barycentricSpace := by
    apply ContinuousMap.ext
    intro x
    exact (realizationHomeomorph ends).apply_symm_apply x
  rw [h]

noncomputable def sectionIncidenceHomology (ends : I → Bool → V)
    (s : C(carrier ends, X)) :
    LinearMap.ker (incidenceBoundary (K := ZMod 2) ends) →ₗ[ZMod 2]
      ↑((TopCat.toSSet.obj (TopCat.of X)).homology
        (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) 1) :=
  (moduleHomologyMap (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) s 1).hom.comp
    (carrierIncidenceHomology ends)

theorem sectionIncidenceHomology_injective (ends : I → Bool → V)
    (q : C(X, carrier ends)) (s : C(carrier ends, X))
    (H : (q.comp s).Homotopic (ContinuousMap.id (carrier ends))) :
    Function.Injective (sectionIncidenceHomology ends s) :=
  (moduleHomologyMap_section_injective _ q s H 1).comp
    (carrierIncidenceHomology_injective ends)

omit [DecidableEq I] in
theorem edge_count_le_cycle_rank_add_vertices (ends : I → Bool → V) :
    Fintype.card I ≤
      Module.finrank (ZMod 2) (LinearMap.ker (incidenceBoundary (K := ZMod 2) ends)) +
        Fintype.card V := by
  have heq := (incidenceBoundary (K := ZMod 2) ends).finrank_range_add_finrank_ker
  have hle := Submodule.finrank_le (LinearMap.range (incidenceBoundary (K := ZMod 2) ends))
  rw [Module.finrank_pi] at heq hle
  omega

theorem edge_count_le_homology_rank_add_vertices (ends : I → Bool → V)
    (q : C(X, carrier ends)) (s : C(carrier ends, X))
    (H : (q.comp s).Homotopic (ContinuousMap.id (carrier ends)))
    [Module.Finite (ZMod 2) ↑((TopCat.toSSet.obj (TopCat.of X)).homology
      (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) 1)] :
    Fintype.card I ≤ Module.finrank (ZMod 2)
      ↑((TopCat.toSSet.obj (TopCat.of X)).homology
        (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) 1) + Fintype.card V := by
  exact (edge_count_le_cycle_rank_add_vertices ends).trans
    (Nat.add_le_add_right
      (LinearMap.finrank_le_finrank_of_injective
        (sectionIncidenceHomology_injective ends q s H)) _)

end PoincareConjecture.M76.CutGraph
