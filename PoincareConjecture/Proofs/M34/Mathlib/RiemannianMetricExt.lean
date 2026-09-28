import Mathlib.Geometry.Manifold.VectorBundle.Riemannian








set_option autoImplicit false

open Bundle
open scoped ContDiff

namespace Bundle.ContMDiffRiemannianMetric

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]



theorem eq_of_inner_eq {g g' : ContMDiffRiemannianMetric IB n F E}
    (h : ∀ x, g.inner x = g'.inner x) : g = g' := by
  cases g
  cases g'
  cases funext h
  rfl

end Bundle.ContMDiffRiemannianMetric
