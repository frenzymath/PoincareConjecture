import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! Differential of an open-submanifold inclusion. Adapted from LeeRiemannian,
`LeeLib/Geometry/OpenSubmanifold.lean`, revision f47f76169b0f914d07661d052117fba97bd9852a. -/

set_option backward.isDefEq.respectTransparency false

open Set Function Manifold Metric TopologicalSpace
open scoped Manifold Topology ContDiff

namespace Poincare.Geometry.Manifold.RegularLevel

noncomputable section

/-! ## The inclusion of an open submanifold of an arbitrary manifold -/

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **The chart representation of an open-submanifold inclusion is the identity**
on the chart's target.

`U`'s chart at `x` is `M`'s chart at `↑x` restricted, so
`writtenInExtChartAt I I x ι` is definitionally `extChartAt I x ∘ (extChartAt I x).symm`;
the claim is then just `PartialEquiv.right_inv`.  The filter is `𝓝[range I]`, not
`𝓝`: off `range I` the chart's inverse is not a right inverse, so the unrestricted
statement is false in general (it holds for boundaryless `I`, where `range I = univ`). -/
theorem writtenInExtChartAt_opens_subtypeVal (U : Opens M) (x : U) :
    writtenInExtChartAt I I x (fun y : U => (y : M))
      =ᶠ[𝓝[range I] (extChartAt I x x)] id := by
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x] with z hz
  exact (extChartAt I x).right_inv hz

/-- **The inclusion of an open submanifold has the identity as its differential.**

Both `T_x U` and `T_{↑x} M` are `E`, and `U`'s charts are `M`'s charts restricted,
so the chart representation of `ι` is the identity where it is defined. -/
theorem hasMFDerivAt_opens_subtypeVal (U : Opens M) (x : U) :
    HasMFDerivAt I I (fun y : U => (y : M)) x (ContinuousLinearMap.id ℝ E) := by
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  refine (hasFDerivWithinAt_id _ _).congr_of_eventuallyEq
    (writtenInExtChartAt_opens_subtypeVal U x) ?_
  exact (extChartAt I x).right_inv (mem_extChartAt_target x)

/-- `dι_x = id` for the inclusion `ι : U ↪ M` of an open submanifold. -/
theorem mfderiv_opens_subtypeVal (U : Opens M) (x : U) :
    mfderiv I I (fun y : U => (y : M)) x = ContinuousLinearMap.id ℝ E :=
  (hasMFDerivAt_opens_subtypeVal U x).mfderiv

/-- `dι_x v = v`: the pointwise form of `mfderiv_opens_subtypeVal`, which is the
shape in which the computation is actually used. -/
@[simp] theorem mfderiv_opens_subtypeVal_apply (U : Opens M) (x : U) (v : TangentSpace I x) :
    (mfderiv I I (fun y : U => (y : M)) x) v = (show E from v) := by
  rw [mfderiv_opens_subtypeVal]; rfl

/-- The inclusion of an open submanifold is an immersion — immediate from
`mfderiv_opens_subtypeVal`, and the hypothesis `pullbackMetric` needs. -/
theorem injective_mfderiv_opens_subtypeVal (U : Opens M) (x : U) :
    Function.Injective (mfderiv I I (fun y : U => (y : M)) x) := by
  intro v w h
  simpa using h

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-- **Restricting a map to an open submanifold does not change its differential.**

`d(F ∘ ι)_x = dF_{↑x} ∘ dι_x = dF_{↑x}`, since `dι_x = id`.  This is the step that
lets a statement about `F` on an open subset be read off from the statement about
`F` on the whole manifold — in particular it is what makes `c` a *regular value*
of `f|_ℛ` on the regular set `ℛ` of `f`, by construction rather than by
hypothesis. -/
theorem mfderiv_opens_restrict (U : Opens M) (F : M → M') {x : U}
    (hF : MDifferentiableAt I I' F ↑x) :
    mfderiv I I' (fun y : U => F ↑y) x = mfderiv I I' F ↑x := by
  have hcomp : mfderiv I I' ((fun z : M => F z) ∘ (fun y : U => (y : M))) x
      = (mfderiv I I' F ↑x).comp (mfderiv I I (fun y : U => (y : M)) x) :=
    mfderiv_comp x hF (hasMFDerivAt_opens_subtypeVal U x).mdifferentiableAt
  rw [Function.comp_def] at hcomp
  rw [hcomp, mfderiv_opens_subtypeVal]
  ext v
  rfl

end General

end

end Poincare.Geometry.Manifold.RegularLevel
