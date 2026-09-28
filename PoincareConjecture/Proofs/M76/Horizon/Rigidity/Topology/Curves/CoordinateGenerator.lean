import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PeriodCircleLoop
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.RetractionFundamentalGroup
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.CircleGroups.IntegerWinding
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.PrimitiveTorusBand
import Mathlib.GroupTheory.OrderOfElement

set_option autoImplicit false

open Set Topology

namespace AddCircle

variable (p : ℝ) [Fact (0 < p)]

theorem periodLoop_class_not_isOfFinOrder :
    ¬ IsOfFinOrder (G := FundamentalGroup (AddCircle p) 0)
      (Path.Homotopic.Quotient.mk (periodLoop p)) := by
  let e := PoincareConjecture.M76.HamiltonIntervalTorus.circleFundamentalGroupEquivInt
    p (Fact.out : 0 < p) 0
  intro h
  have hfin : IsOfFinOrder (e (Path.Homotopic.Quotient.mk (periodLoop p))) :=
    (Function.Injective.isOfFinOrder_iff (f := e.toMonoidHom) e.injective).mpr h
  exact periodLoop_class_ne_one p (e.injective (hfin.eq_one'.trans e.map_one.symm))

theorem periodLoop_class_orderOf :
    orderOf (G := FundamentalGroup (AddCircle p) 0)
      (Path.Homotopic.Quotient.mk (periodLoop p)) = 0 :=
  orderOf_eq_zero_iff.mpr (periodLoop_class_not_isOfFinOrder p)

end AddCircle

namespace PoincareConjecture.M76

variable {X : Type*} [TopologicalSpace X] {p : ℝ} [Fact (0 < p)]

theorem coordinate_periodLoop_not_isOfFinOrder
    (f : C(AddCircle p, X)) (r : C(X, AddCircle p))
    (h : Function.LeftInverse r f) :
    ¬ IsOfFinOrder (G := FundamentalGroup X (f 0)) (Path.Homotopic.Quotient.mk
      ((AddCircle.periodLoop p).map f.continuous)) := by
  have hinj := FundamentalGroup.map_injective_of_leftInverse f r h 0
  exact fun hf => AddCircle.periodLoop_class_not_isOfFinOrder p
    ((Function.Injective.isOfFinOrder_iff (f := FundamentalGroup.map f 0) hinj).mp hf)

theorem coordinate_periodLoop_not_homotopic_refl
    (f : C(AddCircle p, X)) (r : C(X, AddCircle p))
    (h : Function.LeftInverse r f) :
    ¬ ((AddCircle.periodLoop p).map f.continuous).Homotopic (Path.refl (f 0)) := by
  intro hc
  have heq : Path.Homotopic.Quotient.mk
      ((AddCircle.periodLoop p).map f.continuous) = (1 : FundamentalGroup X (f 0)) :=
    Path.Homotopic.Quotient.eq.mpr hc
  exact coordinate_periodLoop_not_isOfFinOrder f r h (heq.symm ▸ IsOfFinOrder.one)

theorem band_center_periodLoop_not_isOfFinOrder {r : ℝ} (hr : 0 ≤ r)
    (b : C(AddCircle p × Icc (-r) r, X)) (retract : C(X, AddCircle p))
    (h : ∀ z, retract (b z) = z.1) :
    let center : C(AddCircle p, X) :=
      b.comp ⟨fun t => (t, (⟨0, by constructor <;> linarith⟩ : Icc (-r) r)),
        continuous_id.prodMk continuous_const⟩
    ¬ IsOfFinOrder (G := FundamentalGroup X (center 0)) (Path.Homotopic.Quotient.mk
      ((AddCircle.periodLoop p).map center.continuous)) := by
  intro center
  exact coordinate_periodLoop_not_isOfFinOrder center retract (fun t => h _)

namespace LinearTorus

omit [Fact (0 < p)] in

theorem primitive_circle_retract {a b : ℤ} (hab : Int.gcd a b = 1) :
    ∃ retract : C(AddCircle p × AddCircle p, AddCircle p),
      ∀ t : AddCircle p, retract (a • t, b • t) = t := by
  let H := integerMatrixHomeomorph p (primitiveMatrix a b) (det_primitiveMatrix hab)
  refine ⟨⟨fun z => (H.symm z).1, H.symm.continuous.fst⟩, ?_⟩
  intro t
  have heq : H (t, 0) = (a • t, b • t) := by
    simp [H, integerMatrixHomeomorph, primitiveMatrix]
  change (H.symm (a • t, b • t)).1 = t
  rw [← heq, H.symm_apply_apply]

theorem primitive_periodLoop_not_isOfFinOrder {a b : ℤ} (hab : Int.gcd a b = 1) :
    let center : C(AddCircle p, AddCircle p × AddCircle p) :=
      ⟨fun t => (a • t, b • t), by fun_prop⟩
    ¬ IsOfFinOrder (G := FundamentalGroup (AddCircle p × AddCircle p) (center 0))
      (Path.Homotopic.Quotient.mk ((AddCircle.periodLoop p).map center.continuous)) := by
  intro center
  obtain ⟨retract, hr⟩ := primitive_circle_retract (p := p) hab
  exact coordinate_periodLoop_not_isOfFinOrder center retract hr

end LinearTorus

end PoincareConjecture.M76
