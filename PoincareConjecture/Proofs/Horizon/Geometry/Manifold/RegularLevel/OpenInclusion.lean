import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option backward.isDefEq.respectTransparency false

open Set Function Manifold Metric TopologicalSpace
open scoped Manifold Topology ContDiff

namespace Poincare.Geometry.Manifold.RegularLevel

noncomputable section

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

theorem writtenInExtChartAt_opens_subtypeVal (U : Opens M) (x : U) :
    writtenInExtChartAt I I x (fun y : U => (y : M))
      =ᶠ[𝓝[range I] (extChartAt I x x)] id := by
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x] with z hz
  exact (extChartAt I x).right_inv hz

theorem hasMFDerivAt_opens_subtypeVal (U : Opens M) (x : U) :
    HasMFDerivAt I I (fun y : U => (y : M)) x (ContinuousLinearMap.id ℝ E) := by
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  refine (hasFDerivWithinAt_id _ _).congr_of_eventuallyEq
    (writtenInExtChartAt_opens_subtypeVal U x) ?_
  exact (extChartAt I x).right_inv (mem_extChartAt_target x)

theorem mfderiv_opens_subtypeVal (U : Opens M) (x : U) :
    mfderiv I I (fun y : U => (y : M)) x = ContinuousLinearMap.id ℝ E :=
  (hasMFDerivAt_opens_subtypeVal U x).mfderiv

@[simp] theorem mfderiv_opens_subtypeVal_apply (U : Opens M) (x : U) (v : TangentSpace I x) :
    (mfderiv I I (fun y : U => (y : M)) x) v = (show E from v) := by
  rw [mfderiv_opens_subtypeVal]; rfl

theorem injective_mfderiv_opens_subtypeVal (U : Opens M) (x : U) :
    Function.Injective (mfderiv I I (fun y : U => (y : M)) x) := by
  intro v w h
  simpa using h

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

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
