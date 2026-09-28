import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

set_option autoImplicit false

open Set
open scoped unitInterval

namespace AddCircle

variable (p : ℝ)

def periodLoop : Path (0 : AddCircle p) 0 where
  toFun t := (((t : ℝ) * p : ℝ) : AddCircle p)
  continuous_toFun := (AddCircle.continuous_mk' p).comp (continuous_subtype_val.mul_const p)
  source' := by
    change (((0 : ℝ) * p : ℝ) : AddCircle p) = 0
    rw [zero_mul, coe_zero]
  target' := by
    change (((1 : ℝ) * p : ℝ) : AddCircle p) = 0
    rw [one_mul, coe_period]

variable [Fact (0 < p)]

theorem periodLoop_not_homotopic_refl :
    ¬ (periodLoop p).Homotopic (Path.refl (0 : AddCircle p)) := by
  intro h
  let cov := isCoveringMap_coe p
  let f : C(unitInterval, ℝ) :=
    ⟨fun t => (t : ℝ) * p, continuous_subtype_val.mul_const p⟩
  have h0 : (periodLoop p) 0 = ((0 : ℝ) : AddCircle p) := by
    simp only [Path.source, coe_zero]
  have h1 : (Path.refl (0 : AddCircle p)) 0 = ((0 : ℝ) : AddCircle p) := rfl
  have hf : f = cov.liftPath (periodLoop p).toContinuousMap 0 h0 := by
    apply (cov.eq_liftPath_iff' h0).mpr
    refine ⟨rfl, ?_⟩
    exact zero_mul p
  have hc : cov.liftPath (Path.refl (0 : AddCircle p)).toContinuousMap 0 h1 =
      ContinuousMap.const unitInterval (0 : ℝ) := by
    change cov.liftPath (ContinuousMap.const unitInterval (0 : AddCircle p)) 0 _ = _
    exact cov.liftPath_const rfl
  have he := cov.liftPath_apply_one_eq_of_homotopicRel h 0 h0 h1
  rw [← hf, hc] at he
  have hp : p = 0 := by
    change (1 : ℝ) * p = 0 at he
    simpa only [one_mul] using he
  exact (Fact.out : 0 < p).ne' hp

theorem periodLoop_class_ne_one :
    Path.Homotopic.Quotient.mk (periodLoop p) ≠
      (1 : FundamentalGroup (AddCircle p) 0) := by
  intro h
  exact periodLoop_not_homotopic_refl p (Path.Homotopic.Quotient.exact h)

theorem nontrivial_fundamentalGroup_zero :
    Nontrivial (FundamentalGroup (AddCircle p) 0) :=
  ⟨⟨Path.Homotopic.Quotient.mk (periodLoop p), 1, periodLoop_class_ne_one p⟩⟩

end AddCircle
