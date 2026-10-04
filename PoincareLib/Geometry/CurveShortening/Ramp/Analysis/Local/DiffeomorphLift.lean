import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Regularity of continuous lifts through local diffeomorphisms

A continuous lift is locally the smooth inverse composed with its projection.
This supplies the C2 lift in Definition 19.12, MT2007 p. 446; see
`proof-work/tasks/M63/derivations/2026-09-21-positive-degree.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

/-- A continuous lift inherits differentiability order from its projection
through a sufficiently regular local diffeomorphism. This is the local
inverse step for the ramp lift in Definition 19.12, MT2007 p. 446. -/
theorem IsLocalDiffeomorphAt.contMDiffAt_of_comp
    {K : Type*} [NontriviallyNormedField K]
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F] [NormedAddCommGroup G] [NormedSpace K G]
    {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
    {I : ModelWithCorners K E H} {J : ModelWithCorners K F H'}
    {J' : ModelWithCorners K G H''}
    {A B C : Type*} [TopologicalSpace A] [ChartedSpace H A]
    [TopologicalSpace B] [ChartedSpace H' B] [TopologicalSpace C] [ChartedSpace H'' C]
    {f : A → B} {p : B → C} {x : A} {m k : WithTop ℕ∞}
    (hp : IsLocalDiffeomorphAt J J' k p (f x)) (hmk : m ≤ k)
    (hf : ContinuousAt f x) (hcomp : ContMDiffAt I J' m (p ∘ f) x) :
    ContMDiffAt I J m f x := by
  have h := (hp.localInverse_contMDiffAt.of_le hmk).comp x hcomp
  apply h.congr_of_eventuallyEq
  exact (hp.localInverse_eventuallyEq_left.comp_tendsto hf).symm
