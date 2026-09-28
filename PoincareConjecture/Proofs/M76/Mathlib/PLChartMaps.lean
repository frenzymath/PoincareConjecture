import PoincareConjecture.Proofs.M76.Mathlib.PLChartFamilies
import PoincareConjecture.Proofs.M76.Mathlib.SupportedCircleQuarterTurn

set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E F X Y ι κ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace X] [TopologicalSpace Y]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in

theorem plInCharts_inverseChart (Q : ι → OpenPartialHomeomorph E X)
    (A : OpenPartialHomeomorph F X)
    (hA : ∀ i, LocallyPiecewiseAffineOn ((Q i).trans A.symm)
      ((Q i).trans A.symm).source) :
    PLInCharts Q (realCharts F) A.symm A.target := by
  apply plInCharts_real_target Q A.symm A.target A.open_target A.continuousOn_invFun
  intro i
  exact hA i

omit [FiniteDimensional ℝ F] in

theorem plInCharts_homeomorph (Q : ι → OpenPartialHomeomorph E X)
    (R : κ → OpenPartialHomeomorph F Y) (H : X ≃ₜ Y)
    (hH : ∀ i j, LocallyPiecewiseAffineOn
      ((Q i).trans (H.toOpenPartialHomeomorph.trans (R j).symm))
      ((Q i).trans (H.toOpenPartialHomeomorph.trans (R j).symm)).source) :
    PLInCharts Q R H univ := by
  refine ⟨isOpen_univ, H.continuous.continuousOn, ?_⟩
  intro i j
  exact (hH i j).mono
    (isOpen_chartMapDomain (Q i) (R j) H univ isOpen_univ H.continuous.continuousOn)
    (fun _ hx => ⟨hx.1.1, mem_univ _, hx.2⟩)

end Geometry

namespace AddCircle

variable (p : ℝ) [Fact (0 < p)]

theorem plInCharts_coe :
    PLInCharts (realCharts ℝ) (quotientCharts p) ((↑) : ℝ → AddCircle p) univ := by
  refine ⟨isOpen_univ, (AddCircle.continuous_mk' p).continuousOn, ?_⟩
  intro i a
  let D := chartMapDomain (realCharts ℝ i) (quotientCharts p a)
    ((↑) : ℝ → AddCircle p) univ
  have hD : IsOpen D := isOpen_chartMapDomain _ _ _ _ isOpen_univ
    (AddCircle.continuous_mk' p).continuousOn
  change LocallyPiecewiseAffineOn (toIcoMod (Fact.out : 0 < p) a) D
  exact locallyPiecewiseAffineOn_toIcoMod (Fact.out : 0 < p) a hD (fun _ hx => hx.2)

theorem plInCharts_shortArc_inverse (d : ℝ) :
    PLInCharts (quotientCharts p) (realCharts ℝ)
      (shortArcQuotient p d).symm (shortArcQuotient p d).target :=
  plInCharts_inverseChart (quotientCharts p) (shortArcQuotient p d)
    (fun a => (mem_piecewiseAffineGroupoid_iff ℝ _).mp
      (shortArcQuotient_transition_mem_piecewiseAffineGroupoid p d a) |>.1)

theorem plInCharts_cylinder_homeomorph
    (H : (AddCircle p × ℝ) ≃ₜ (AddCircle p × ℝ))
    (hH : ∀ a b : ℝ,
      let A := (openPartialHomeomorphCoe p a).prod (OpenPartialHomeomorph.refl ℝ)
      let B := (openPartialHomeomorphCoe p b).prod (OpenPartialHomeomorph.refl ℝ)
      A.trans (H.toOpenPartialHomeomorph.trans B.symm) ∈ piecewiseAffineGroupoid (ℝ × ℝ)) :
    PLInCharts (prodCharts (quotientCharts p) (realCharts ℝ))
      (prodCharts (quotientCharts p) (realCharts ℝ)) H univ ∧
    PLInCharts (prodCharts (quotientCharts p) (realCharts ℝ))
      (prodCharts (quotientCharts p) (realCharts ℝ)) H.symm univ := by
  let Q := prodCharts (quotientCharts p) (realCharts ℝ)
  constructor
  · apply plInCharts_homeomorph Q Q H
    intro i j
    exact (mem_piecewiseAffineGroupoid_iff (ℝ × ℝ) _).mp (hH i.1 j.1) |>.1
  · apply plInCharts_homeomorph Q Q H.symm
    intro i j
    have h := (mem_piecewiseAffineGroupoid_iff (ℝ × ℝ) _).mp (hH j.1 i.1) |>.2
    exact h.mono ((Q i).trans (H.symm.toOpenPartialHomeomorph.trans (Q j).symm)).open_source
      (fun _ hz => ⟨⟨hz.1, mem_univ _⟩, hz.2.2⟩)

end AddCircle
