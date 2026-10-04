import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.SupportedNerve
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.OrderComplexSimplex
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.OrderComplexNeighborhoods

/-!
# Actual characteristic maps on supported lifted subcomplexes

A characteristic simplex with vertices in s has total selected weight one.
Its lift therefore lies in the actual inverse image of the open coordinate
neighborhood U_s. These characteristic maps commute literally with every
inclusion s subset t and with the map to all singular simplices.
Source: Hatcher, Theorem 2.27, printed pp. 128-130.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace PoincareMT.Proofs.M59

open M02.Topology

variable {J : Type u} [PartialOrder J] [Fintype J]

/-- An actual characteristic simplex on selected vertices is entirely
inside their coordinate neighborhood. Source: Hatcher, Theorem 2.27. -/
theorem orderComplexSimplex_mem_neighborhood (s : Finset J) {n : ℕ}
    (z : (supportedNerve s).toSSet _⦋n⦌) (t : stdSimplex ℝ (Fin (n + 1))) :
    orderComplexSimplex z.val t ∈ orderComplexNeighborhood s := by
  classical
  have hsupp (j : J) (hj : j ∉ s) : (orderComplexSimplex z.val t).val j = 0 := by
    change FunOnFinite.linearMap ℝ ℝ z.val.obj t.val j = 0
    rw [FunOnFinite.linearMap_apply_apply]
    apply Finset.sum_eq_zero
    intro i hi
    exact (hj ((Finset.mem_filter.mp hi).2 ▸ z.property i)).elim
  change 0 < orderComplexRestrictionWeight s _
  rw [orderComplexRestrictionWeight_eq_one s _ hsupp]
  exact zero_lt_one

variable {E : Type u} [TopologicalSpace E] (p : C(E, (finiteOrderComplex J).space))

/-- The actual inverse image of a selected coordinate neighborhood.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
def liftedCoordinateNeighborhood (s : Finset J) : Set E :=
  p ⁻¹' orderComplexNeighborhood s

/-- A supported characteristic simplex, restricted to its actual
covering neighborhood. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
def supportedLiftSimplex (s : Finset J) {n : ℕ}
    (z : (supportedSingularLift p (orderComplexSingular J) s).toSSet _⦋n⦌) :
    C(stdSimplex ℝ (Fin (n + 1)), liftedCoordinateNeighborhood p s) := by
  refine ⟨fun t => ⟨(TopCat.of E).toSSetObjEquiv _ z.val.val.2 t, ?_⟩, ?_⟩
  · change p ((TopCat.of E).toSSetObjEquiv _ z.val.val.2 t) ∈
      orderComplexNeighborhood s
    have h := congrArg (fun a => (TopCat.of (finiteOrderComplex J).space).toSSetObjEquiv _ a t)
      z.val.property
    change p ((TopCat.of E).toSSetObjEquiv _ z.val.val.2 t) =
      orderComplexSimplex z.val.val.1 t at h
    rw [h]
    exact orderComplexSimplex_mem_neighborhood s ⟨z.val.val.1, z.property⟩ t
  · exact ((TopCat.of E).toSSetObjEquiv _ z.val.val.2).continuous.subtype_mk _

/-- The actual characteristic-simplex comparison on a supported lifted
subcomplex, valued in its open covering neighborhood.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
def supportedSingularComparison (s : Finset J) :
    (supportedSingularLift p (orderComplexSingular J) s).toSSet ⟶
      TopCat.toSSet.obj (TopCat.of (liftedCoordinateNeighborhood p s)) :=
  singularMapOfContinuousSimplices _ _ (fun _ z => supportedLiftSimplex p s z) (by
    intro n m f z
    ext t : 1
    apply Subtype.ext
    rfl)

/-- Projection of the supported comparison gives the original literal
singular projection of the lifted model. Source: Hatcher, Theorem 2.27. -/
theorem supportedSingularComparison_projection (s : Finset J) :
    supportedSingularComparison p s ≫ TopCat.toSSet.map
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ :
          C(liftedCoordinateNeighborhood p s, E))) =
      (supportedSingularLift p (orderComplexSingular J) s).ι ≫
        singularLiftProjection p (nerve J) (orderComplexSingular J) := by
  ext n : 1
  apply ConcreteCategory.hom_ext
  intro z
  apply ((TopCat.of E).toSSetObjEquiv n).injective
  rfl

/-- The actual inclusion between lifted coordinate neighborhoods.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
def liftedCoordinateNeighborhoodInclusion {s t : Finset J} (h : s ⊆ t) :
    C(liftedCoordinateNeighborhood p s, liftedCoordinateNeighborhood p t) :=
  ⟨fun e => ⟨e.val, orderComplexNeighborhood_mono h e.property⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- Selected-set inclusions commute with the actual characteristic
comparisons. Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem supportedSingularComparison_naturality {s t : Finset J} (h : s ⊆ t) :
    SSet.Subcomplex.homOfLE (show supportedSingularLift p (orderComplexSingular J) s ≤
        supportedSingularLift p (orderComplexSingular J) t from
          fun _ _ hz i => h (hz i)) ≫
      supportedSingularComparison p t =
    supportedSingularComparison p s ≫ TopCat.toSSet.map
      (TopCat.ofHom (liftedCoordinateNeighborhoodInclusion p h)) := by
  ext n : 1
  apply ConcreteCategory.hom_ext
  intro z
  apply ((TopCat.of (liftedCoordinateNeighborhood p t)).toSSetObjEquiv n).injective
  rfl

end PoincareMT.Proofs.M59
