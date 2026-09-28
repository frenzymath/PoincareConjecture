import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Algebra.Module.LocallyConvex

set_option autoImplicit false

open Set Topology

namespace PoincareConjecture.M76.LinearTorus

variable (p : ℝ)

def quotientMap : C(ℝ × ℝ, AddCircle p × AddCircle p) :=
  ⟨fun x => ((x.1 : AddCircle p), (x.2 : AddCircle p)),
    (AddCircle.continuous_mk' p).prodMap (AddCircle.continuous_mk' p)⟩

@[simp] theorem quotientMap_apply (x : ℝ × ℝ) :
    quotientMap p x = ((x.1 : AddCircle p), (x.2 : AddCircle p)) := rfl

@[simp] theorem quotientMap_zero : quotientMap p 0 = 0 := by simp

theorem isOpenQuotientMap_quotientMap : IsOpenQuotientMap (quotientMap p) :=
  (AddCircle.isAddQuotientCoveringMap_coe p).isOpenQuotientMap.prodMap
    (AddCircle.isAddQuotientCoveringMap_coe p).isOpenQuotientMap

theorem exists_real_lift (f : C(AddCircle p × AddCircle p, AddCircle p)) :
    ∃ F : C(ℝ × ℝ, ℝ), ∀ x, (F x : AddCircle p) = f (quotientMap p x) := by
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk_surjective (f (quotientMap p 0))
  obtain ⟨F, ⟨_, hF⟩, _⟩ := (AddCircle.isCoveringMap_coe p).existsUnique_continuousMap_lifts
    (f.comp (quotientMap p)) 0 c hc
  exact ⟨F, fun x => congrFun hF x⟩

theorem real_lift_deck_difference
    (f : C(AddCircle p × AddCircle p, AddCircle p)) (F : C(ℝ × ℝ, ℝ))
    (hF : ∀ x, (F x : AddCircle p) = f (quotientMap p x))
    (v : ℝ × ℝ) (hv : quotientMap p v = 0) (x : ℝ × ℝ) :
    F (x + v) - F x = F v - F 0 := by
  have hq (y : ℝ × ℝ) : quotientMap p (y + v) = quotientMap p y := by
    have hv₁ : (v.1 : AddCircle p) = 0 := congrArg Prod.fst hv
    have hv₂ : (v.2 : AddCircle p) = 0 := congrArg Prod.snd hv
    change ((↑(y.1 + v.1) : AddCircle p), (↑(y.2 + v.2) : AddCircle p)) = _
    simp only [AddCircle.coe_add, hv₁, hv₂, add_zero, quotientMap_apply]
  exact (AddCircle.isCoveringMap_coe p).const_of_comp
    (F.continuous.comp (continuous_id.add continuous_const) |>.sub F.continuous)
    (fun y z => by simp [hF, hq]) x 0 |>.trans (by simp)

theorem exists_integer_periods
    (f : C(AddCircle p × AddCircle p, AddCircle p)) (F : C(ℝ × ℝ, ℝ))
    (hF : ∀ x, (F x : AddCircle p) = f (quotientMap p x)) :
    ∃ n m : ℤ,
      (∀ x y, F (x + p, y) = F (x, y) + n • p) ∧
      (∀ x y, F (x, y + p) = F (x, y) + m • p) := by
  have hp₁ : quotientMap p (p, 0) = 0 := by simp
  have hp₂ : quotientMap p (0, p) = 0 := by simp
  have hn : ((F (p, 0) - F 0 : ℝ) : AddCircle p) = 0 := by
    rw [AddCircle.coe_sub, hF, hF, hp₁, quotientMap_zero, sub_self]
  have hm : ((F (0, p) - F 0 : ℝ) : AddCircle p) = 0 := by
    rw [AddCircle.coe_sub, hF, hF, hp₂, quotientMap_zero, sub_self]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff p).mp hn
  obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff p).mp hm
  refine ⟨n, m, ?_, ?_⟩
  · intro x y
    have h := real_lift_deck_difference p f F hF (p, 0) hp₁ (x, y)
    simpa [← hn, sub_eq_iff_eq_add, add_comm] using h
  · intro x y
    have h := real_lift_deck_difference p f F hF (0, p) hp₂ (x, y)
    simpa [← hm, sub_eq_iff_eq_add, add_comm] using h

end PoincareConjecture.M76.LinearTorus
