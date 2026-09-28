import Mathlib.Geometry.Manifold.VectorBundle.Pullback









set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace Bundle

variable {B C EB EC HB HC F : Type*}
  [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup EC] [NormedSpace ℝ EC]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace HB] [TopologicalSpace HC]
  {IB : ModelWithCorners ℝ EB HB} {IC : ModelWithCorners ℝ EC HC}
  [TopologicalSpace B] [TopologicalSpace C]
  [ChartedSpace HB B] [ChartedSpace HC C]
  {E : B → Type*} [∀ b, Nonempty (E b)]
  [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
  [FiberBundle F E] {k : ℕ∞ω}


set_option backward.isDefEq.respectTransparency false in


theorem contMDiffWithinAt_pullback_section_iff
    (f : ContMDiffMap IC IB C B k) (v : ∀ z : C, E (f z))
    (S : Set C) (z : C) :
    ContMDiffWithinAt IC (IC.prod 𝓘(ℝ, F)) k
        (fun w => TotalSpace.mk' F (E := (f : C → B) *ᵖ E) w (v w)) S z ↔
      ContMDiffWithinAt IC (IB.prod 𝓘(ℝ, F)) k
        (fun w => TotalSpace.mk' F (f w) (v w)) S z := by
  rw [contMDiffWithinAt_section, contMDiffWithinAt_totalSpace]
  change ContMDiffWithinAt IC 𝓘(ℝ, F) k
      (fun w => (trivializationAt F E (f z) (TotalSpace.mk' F (f w) (v w))).2) S z ↔
    ContMDiffWithinAt IC IB k f S z ∧ _
  exact (and_iff_right (f.contMDiff z).contMDiffWithinAt).symm

end Bundle
