import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn











set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology NNReal

namespace PoincareConjecture.M14

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]





theorem exists_open_approximatesLinearOn {f : E → F} {S : Set E}
    (hSc : Convex ℝ S) (hS : UniqueDiffOn ℝ S) (hf : ContDiffOn ℝ 1 f S)
    {x : E} (hx : x ∈ S) (c : ℝ≥0) (hc : 0 < c) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
      ApproximatesLinearOn f (fderivWithin ℝ f S x) (U ∩ S) c := by
  let L := fderivWithin ℝ f S x
  let D : E → E →L[ℝ] F := fun y => fderivWithin ℝ f S y - L
  have hder (y : E) (hy : y ∈ S) :
      HasFDerivWithinAt (fun z => f z - L z) (D y) S y :=
    (hf.differentiableOn_one y hy).hasFDerivWithinAt.sub L.hasFDerivAt.hasFDerivWithinAt
  have hcont : ContinuousWithinAt D S x :=
    (hf.continuousOn_fderivWithin hS le_rfl x hx).sub continuousWithinAt_const
  have hzero : ‖D x‖₊ < c := by simpa only [D, L, sub_self, nnnorm_zero] using hc
  obtain ⟨V, hV, hLip⟩ :=
    hSc.exists_nhdsWithin_lipschitzOnWith_of_hasFDerivWithinAt_of_nnnorm_lt
      (eventually_nhdsWithin_of_forall hder) hcont c hzero
  obtain ⟨U, hU, hxU, hUV⟩ := mem_nhdsWithin.mp hV
  exact ⟨U, hU, hxU, (hLip.mono hUV).approximatesLinearOn⟩

end PoincareConjecture.M14
