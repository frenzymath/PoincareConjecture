import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CircleClosedArc

set_option autoImplicit false
open Set

namespace AddCircle

noncomputable def closedArcCoordinates (p a b : ℝ) [Fact (0 < p)]
    (hgap : b < a + p) : Icc a b ≃ₜ closedIntervalArc p a b := by
  have hinj : InjOn (fun t : ℝ => (t : AddCircle p)) (Icc a b) := by
    intro x hx y hy hxy
    exact (coe_eq_coe_iff_of_mem_Ico
      (show x ∈ Ico a (a + p) from ⟨hx.1, hx.2.trans_lt hgap⟩)
      (show y ∈ Ico a (a + p) from ⟨hy.1, hy.2.trans_lt hgap⟩)).mp hxy
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.Set.imageOfInjOn (fun t : ℝ => (t : AddCircle p)) (Icc a b) hinj)
    (((AddCircle.continuous_mk' p).comp continuous_subtype_val).subtype_mk _)

@[simp] theorem closedArcCoordinates_coe (p a b : ℝ) [Fact (0 < p)]
    (hgap : b < a + p) (t : Icc a b) :
    (closedArcCoordinates p a b hgap t : AddCircle p) = (t : ℝ) := rfl

@[simp] theorem closedArcCoordinates_symm_coe (p a b : ℝ) [Fact (0 < p)]
    (hgap : b < a + p) (z : closedIntervalArc p a b) :
    (((closedArcCoordinates p a b hgap).symm z : ℝ) : AddCircle p) = z :=
  congrArg Subtype.val ((closedArcCoordinates p a b hgap).apply_symm_apply z)

noncomputable def liftToClosedArc {Y : Type*} [TopologicalSpace Y]
    {p a b : ℝ} [Fact (0 < p)] (hgap : b < a + p)
    (q : C(Y, AddCircle p)) (hq : ∀ y, q y ∈ closedIntervalArc p a b) : C(Y, ℝ) :=
  ⟨fun y => (closedArcCoordinates p a b hgap).symm ⟨q y, hq y⟩,
    continuous_subtype_val.comp ((closedArcCoordinates p a b hgap).symm.continuous.comp
      (q.continuous.subtype_mk _))⟩

theorem liftToClosedArc_mem {Y : Type*} [TopologicalSpace Y]
    {p a b : ℝ} [Fact (0 < p)] (hgap : b < a + p)
    (q : C(Y, AddCircle p)) (hq : ∀ y, q y ∈ closedIntervalArc p a b) (y : Y) :
    liftToClosedArc hgap q hq y ∈ Icc a b :=
  ((closedArcCoordinates p a b hgap).symm ⟨q y, hq y⟩).property

@[simp] theorem liftToClosedArc_coe {Y : Type*} [TopologicalSpace Y]
    {p a b : ℝ} [Fact (0 < p)] (hgap : b < a + p)
    (q : C(Y, AddCircle p)) (hq : ∀ y, q y ∈ closedIntervalArc p a b) (y : Y) :
    (liftToClosedArc hgap q hq y : AddCircle p) = q y :=
  closedArcCoordinates_symm_coe p a b hgap ⟨q y, hq y⟩

theorem liftToClosedArc_eq_iff {Y : Type*} [TopologicalSpace Y]
    {p a b : ℝ} [Fact (0 < p)] (hgap : b < a + p)
    (q : C(Y, AddCircle p)) (hq : ∀ y, q y ∈ closedIntervalArc p a b)
    (y : Y) {t : ℝ} (ht : t ∈ Icc a b) :
    liftToClosedArc hgap q hq y = t ↔ q y = (t : AddCircle p) := by
  constructor
  · intro h
    rw [← liftToClosedArc_coe hgap q hq y, h]
  · intro h
    exact (coe_eq_coe_iff_of_mem_Ico
      (show liftToClosedArc hgap q hq y ∈ Ico a (a + p) from
        ⟨(liftToClosedArc_mem hgap q hq y).1, (liftToClosedArc_mem hgap q hq y).2.trans_lt hgap⟩)
      (show t ∈ Ico a (a + p) from ⟨ht.1, ht.2.trans_lt hgap⟩)).mp
      ((liftToClosedArc_coe hgap q hq y).trans h)

theorem liftToClosedArc_eq_chart {Y : Type*} [TopologicalSpace Y]
    {p a b cut : ℝ} [Fact (0 < p)] (ha : cut < a) (hb : b < cut + p)
    (q : C(Y, AddCircle p)) (hq : ∀ y, q y ∈ closedIntervalArc p a b) (y : Y) :
    liftToClosedArc (by linarith : b < a + p) q hq y =
      (openPartialHomeomorphCoe p cut).symm (q y) := by
  let J := openPartialHomeomorphCoe p cut
  have ht := liftToClosedArc_mem (by linarith : b < a + p) q hq y
  have h := J.left_inv ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  change J.symm ((liftToClosedArc (by linarith : b < a + p) q hq y : ℝ) : AddCircle p) = _ at h
  rw [liftToClosedArc_coe] at h
  exact h.symm

end AddCircle
