import PoincareConjecture.Proofs.M76.Mathlib.AddCirclePLCharts
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffineInverse

set_option autoImplicit false

open Set Geometry

namespace AddCircle

variable (p : ℝ) [Fact (0 < p)]

noncomputable def shortArcQuotient (d : ℝ) : OpenPartialHomeomorph ℝ (AddCircle p) :=
  (openPartialHomeomorphCoe p (-p / 2)).restr (Ioo (-d) d)

theorem shortArcQuotient_source {d : ℝ} (hd : d < p / 2) :
    (shortArcQuotient p d).source = Ioo (-d) d := by
  ext x
  change (x ∈ Ioo (-p / 2) (-p / 2 + p) ∧ x ∈ interior (Ioo (-d) d)) ↔
    x ∈ Ioo (-d) d
  rw [isOpen_Ioo.interior_eq]
  constructor
  · exact And.right
  · intro hx
    exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩, hx⟩

theorem shortArcQuotient_target {d : ℝ} (hd : d < p / 2) :
    (shortArcQuotient p d).target = ((↑) : ℝ → AddCircle p) '' Ioo (-d) d := by
  rw [← (shortArcQuotient p d).image_source_eq_target, shortArcQuotient_source p hd]
  rfl

theorem shortArcQuotient_symm_coe {d x : ℝ} (hd : d < p / 2)
    (hx : x ∈ Ioo (-d) d) :
    (shortArcQuotient p d).symm (x : AddCircle p) = x := by
  exact (shortArcQuotient p d).left_inv (by rwa [shortArcQuotient_source p hd])

theorem shortArcQuotient_transition_mem_piecewiseAffineGroupoid (d a : ℝ) :
    (openPartialHomeomorphCoe p a).trans (shortArcQuotient p d).symm ∈
      piecewiseAffineGroupoid ℝ := by
  let Q := (openPartialHomeomorphCoe p a).trans (shortArcQuotient p d).symm
  apply (mem_piecewiseAffineGroupoid_iff_forward Q).mpr
  have hPL := quotient_chart_transition_locallyPiecewiseAffine p a (-p / 2)
  exact hPL.mono Q.open_source (fun _ hx => ⟨hx.1, hx.2.1⟩)

end AddCircle
