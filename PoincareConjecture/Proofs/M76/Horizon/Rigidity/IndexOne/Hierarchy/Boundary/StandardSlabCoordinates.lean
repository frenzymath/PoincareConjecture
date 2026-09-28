import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Hierarchy.Boundary.StandardAnnulus

set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "D1" => closedBall (0 : Fin 1 → ℝ) 1
local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))
local notation "C" => AddCircle p
local notation "E" => latticeHandleDomainEquiv (Fin 1) (Fin 2) L
local notation "Q" => hamiltonOneHierarchyCoordinates

noncomputable def shortClosedPhaseIntervalCoordinates (a b : ℝ) (hshort : b < a + p) :
    Icc a b ≃ₜ AddCircle.closedIntervalArc p a b := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  have hinj : InjOn (fun t : ℝ => (t : C)) (Icc a b) := by
    intro x hx y hy hxy
    have hxI : x ∈ Ico a (a + p) := ⟨hx.1, hx.2.trans_lt hshort⟩
    have hyI : y ∈ Ico a (a + p) := ⟨hy.1, hy.2.trans_lt hshort⟩
    exact (AddCircle.coe_eq_coe_iff_of_mem_Ico hxI hyI).mp hxy
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn (fun t : ℝ => (t : C)) (Icc a b) hinj)
    (((AddCircle.continuous_mk' p).comp continuous_subtype_val).subtype_mk _)

noncomputable def standardSlabCoordinates (a b : ℝ) (hshort : b < a + p) :
    ((D1 × C) × Icc a b) ≃ₜ sourceSlab (ContinuousMap.id H) a b := by
  let A := shortClosedPhaseIntervalCoordinates a b hshort
  let T : ((D1 × C) × AddCircle.closedIntervalArc p a b) ≃ₜ
      sourceSlab (ContinuousMap.id H) a b := {
    toFun := fun z => ⟨(E).symm ((Q).symm (z.1, z.2.val)), by
      apply (mem_sourceSlab_iff (ContinuousMap.id H) a b _).mpr
      change (Q ((E) ((E).symm ((Q).symm (z.1, z.2.val))))).2 ∈ _
      rw [(E).apply_symm_apply, (Q).apply_symm_apply]
      exact z.2.property⟩
    invFun := fun x => ((Q ((E) ⟨x, sourceSlab_subset (ContinuousMap.id H) a b x.property⟩)).1,
      ⟨(Q ((E) ⟨x, sourceSlab_subset (ContinuousMap.id H) a b x.property⟩)).2,
        (mem_sourceSlab_iff (ContinuousMap.id H) a b _).mp x.property⟩)
    left_inv := by
      intro z
      apply Prod.ext
      · change (Q ((E) ((E).symm ((Q).symm (z.1, z.2.val))))).1 = z.1
        rw [(E).apply_symm_apply, (Q).apply_symm_apply]
      · apply Subtype.ext
        change (Q ((E) ((E).symm ((Q).symm (z.1, z.2.val))))).2 = z.2.val
        rw [(E).apply_symm_apply, (Q).apply_symm_apply]
    right_inv := by
      intro x
      apply Subtype.ext
      change ((E).symm ((Q).symm ((Q ((E) ⟨x, _⟩)).1,
        (Q ((E) ⟨x, _⟩)).2)) : X) = x
      rw [Prod.eta, (Q).symm_apply_apply, (E).symm_apply_apply]
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  exact ((Homeomorph.refl (D1 × C)).prodCongr A).trans T

theorem standardSlabCoordinates_apply (a b : ℝ) (hshort : b < a + p)
    (z : (D1 × C) × Icc a b) :
    (standardSlabCoordinates a b hshort z : X) =
      ((E).symm ((Q).symm (z.1, ((z.2 : ℝ) : C))) : X) := rfl

end PoincareConjecture.M76.HamiltonIntervalTorus
