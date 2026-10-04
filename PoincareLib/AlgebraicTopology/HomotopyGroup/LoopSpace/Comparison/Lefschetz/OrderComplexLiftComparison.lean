import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.SupportedConeComparison
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.SupportedEmptyComparison
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Comparison.Lefschetz.SupportedComparisonGluing
import Mathlib.Order.Preorder.Finite

/-!
# The actual singular comparison for a lifted finite order complex

Induct on a selected finite vertex set, using a minimal vertex. Its
deletion and strict upper link have fewer vertices, and its upper cone
has the proved characteristic comparison. The literal subcomplex square
and matching open neighborhoods give the induction step by Mayer-Vietoris.
At the full selected set, removing only subtype proofs recovers the actual
singular projection of the original lifted model.
Source: Hatcher, Theorem 2.27, printed pp. 128-130.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory HomologicalComplex

universe u

namespace PoincareMT.Proofs.M59

open M02.Topology

variable {J : Type u} [PartialOrder J] [Fintype J]
  {E : Type u} [TopologicalSpace E]
  (p : C(E, (finiteOrderComplex J).space)) (hp : IsCoveringMap p)

include hp in
/-- Every selected characteristic map is a quasi-isomorphism, by the
deletion, cone, and link induction. Source: Hatcher, Theorem 2.27. -/
theorem supportedSingularComparison_quasiIso (s : Finset J) :
    QuasiIso (SSet.chainComplexMap (supportedSingularComparison p s)
      integralCoefficient.{u}) := by
  classical
  refine s.strongInductionOn ?_
  intro s ih
  by_cases hs : s = ∅
  · subst s
    exact supportedSingularComparison_empty_quasiIso p
  obtain ⟨v, hv, hmin⟩ := Finset.exists_minimal (Finset.nonempty_iff_ne_empty.mpr hs)
  have hminimal : ∀ j ∈ s, j ≤ v → j = v := by
    intro j hj hjv
    exact le_antisymm hjv (hmin hj hjv)
  have hl : s.filter (v < ·) ⊂ s := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro h
    have hv' : v ∈ s.filter (v < ·) := h.symm ▸ hv
    exact (lt_irrefl v) (Finset.mem_filter.mp hv').2
  exact supportedSingularComparison_minimal_gluing p s v hminimal
    (ih _ (Finset.erase_ssubset hv))
    (supportedSingularComparison_cone_quasiIso p hp (s.filter (v ≤ ·)) v
      (Finset.mem_filter.mpr ⟨hv, le_rfl⟩)
      (fun _ hj => (Finset.mem_filter.mp hj).2))
    (ih _ hl)

/-- With all vertices selected, the supported lifted subcomplex is
the entire original lifted model. Source: Hatcher, Theorem 2.27. -/
theorem supportedSingularLift_univ :
    supportedSingularLift p (orderComplexSingular J) (Finset.univ : Finset J) = ⊤ := by
  ext n z
  change (∀ i, z.val.1.obj i ∈ Finset.univ) ↔ True
  simp only [Finset.mem_univ, implies_true]

omit hp in
set_option backward.isDefEq.respectTransparency false in
/-- The literal characteristic projection from the lifted finite nerve
to actual singular simplices is an integral quasi-isomorphism. This holds
for every covering, without compactness or connectedness assumptions.
Source: Hatcher, Theorem 2.27, pp. 128-130. -/
theorem orderComplexSingularLift_quasiIso (hp : IsCoveringMap p) :
    QuasiIso (SSet.chainComplexMap
      (singularLiftProjection p (nerve J) (orderComplexSingular J))
        integralCoefficient.{u}) := by
  let D := supportedSingularLift p (orderComplexSingular J) (Finset.univ : Finset J)
  let W := liftedCoordinateNeighborhood p (Finset.univ : Finset J)
  have hW (x : E) : x ∈ W := by
    change p x ∈ orderComplexNeighborhood (Finset.univ : Finset J)
    rw [orderComplexNeighborhood_univ]
    exact Set.mem_univ _
  let e : W ≃ₜ E := {
    toFun := Subtype.val
    invFun := fun x => ⟨x, hW x⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := continuous_subtype_val
    continuous_invFun := continuous_id.subtype_mk hW }
  let : IsIso D.ι := by
    dsimp only [D]
    rw [supportedSingularLift_univ p]
    change IsIso (SSet.Subcomplex.topIso _).hom
    infer_instance
  let := supportedSingularComparison_quasiIso p hp (Finset.univ : Finset J)
  let := homeomorphSingularChainMap_quasiIso e
  let T := (SSet.chainComplexFunctor (ModuleCat.{u} ℤ)).obj integralCoefficient
  have h : QuasiIso (T.map (D.ι ≫
      singularLiftProjection p (nerve J) (orderComplexSingular J))) := by
    rw [← supportedSingularComparison_projection p (Finset.univ : Finset J),
      Functor.map_comp]
    infer_instance
  rw [Functor.map_comp] at h
  exact (quasiIso_iff_comp_left _ _).mp h

end PoincareMT.Proofs.M59
