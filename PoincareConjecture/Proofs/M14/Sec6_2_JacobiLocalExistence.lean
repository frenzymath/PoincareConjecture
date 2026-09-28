import PoincareConjecture.Proofs.M14.Sec6_2_JacobiGaugeResidual
import PoincareConjecture.Proofs.M14.Sec6_2_JacobiGaugeCoordinates
import PoincareConjecture.Proofs.M14.Sec6_2_ClosedJacobiODE
import PoincareConjecture.Proofs.M14.Sec6_2_ClosedFieldExtension









set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  (R : M14SquareRootPath G p) (b : G.gaugeCover.index)




theorem exists_gaugeHorizontalJacobiPair
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (hscalar : ContMDiff (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      (horizontalScalarCurvature G.leafwise))
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (hM04 : RicciFlowCurvatureTheory.{0}) (x₀ : G.gaugeCover.spatial b)
    {a c t₀ : ℝ} (hac : a < c) (hsub : Icc a c ⊆ M14SqrtParameterInterval τ₁ τ₂)
    {β : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b}
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β (Icc a c))
    (hrec : ∀ s ∈ Icc a c, (G.gaugeCover.cylinder b).toSpacetime (β s) = R.curve s)
    (hclock : ∀ s ∈ Icc a c, (β s).1.val = T - s ^ 2)
    (ht₀ : t₀ ∈ Icc a c) (z₀ : G.Horizontal (R.curve t₀) × G.Horizontal (R.curve t₀)) :
    ∃ z : ∀ s, G.Horizontal (R.curve s) × G.Horizontal (R.curve s),
      IsHorizontalJacobiPairOn R a c z ∧ z t₀ = z₀ := by
  let C := Icc a c
  let q := fun s => (β s).2.val
  have hq := gaugeLift_spatialCurve_contDiffOn b hβ
  have hmem : MapsTo q C (extChartAt (𝓡 n) x₀).target := by
    intro s hs
    have hsrc : (β s).2 ∈ (extChartAt (𝓡 n) x₀).source := by
      rw [extChartAt_source, (G.gaugeCover.spatial b).chartAt_source_eq_univ]
      exact mem_univ _
    have he : extChartAt (𝓡 n) x₀ (β s).2 = (β s).2.val := by
      rw [extChartAt_coe]
      rfl
    simpa only [he] using (extChartAt (𝓡 n) x₀).map_source hsrc
  have htime (s : ℝ) (hs : s ∈ C) : T - s ^ 2 ∈ (G.gaugeCover.interval b).domain := by
    rw [← hclock s hs]
    exact (β s).1.property
  obtain ⟨v₀, hv₀⟩ := exists_horizontalGauge_coordinates b (hrec t₀ ht₀) z₀.1
  obtain ⟨p₀, hp₀⟩ := exists_horizontalGauge_coordinates b (hrec t₀ ht₀) z₀.2
  obtain ⟨v, hv₀', hv, hvd⟩ := exists_closedCoordinateJacobi_solution W.flow T x₀ hM04
    hac htime hq hmem ht₀ (v₀, p₀)
  let Y := horizontalFieldOfGauge b hrec (fun s => (v s).1)
  let P := horizontalFieldOfGauge b hrec (fun s => (v s).2)
  have hY := horizontalFieldOfGauge_contMDiffOn b hβ hrec hv.fst
  have hP := horizontalFieldOfGauge_contMDiffOn b hβ hrec hv.snd
  obtain ⟨EY⟩ := exists_pullbackExtension_Icc hac hY
  obtain ⟨EP⟩ := exists_pullbackExtension_Icc hac hP
  have hYcoord := fun s hs => horizontalFieldOfGauge_heq b hrec (fun r => (v r).1) (s := s) hs
  have hPcoord := fun s hs => horizontalFieldOfGauge_heq b hrec (fun r => (v r).2) (s := s) hs
  have hfirst (s : ℝ) (hs : s ∈ C) :
      M14HorizontalCovariantDerivative G R.curve C Y EY s = P s := by
    have hd : derivWithin (fun r => (v r).1) C s =
        (v s).2 - M08.closedChartConnection W.flow T x₀ C (s, q s)
          (derivWithin q C s) (v s).1 :=
      ((ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℝ (Fin n))).hasFDerivAt.comp_hasDerivWithinAt s (hvd s hs)).derivWithin
          (uniqueDiffOn_Icc hac s hs)
    have hDY := horizontalCovariantDerivative_lifted_gauge b hCoordinates W T x₀ hβ hrec
      hclock EY (fun r => (v r).1) hYcoord hs (uniqueDiffOn_Icc hac s hs)
    rw [hd, sub_add_cancel] at hDY
    exact eq_of_heq (hDY.trans (hPcoord s hs).symm)
  have hsecond (s : ℝ) (hs : s ∈ C) (Z : G.Horizontal (R.curve s)) :
      horizontalJacobiPairResidual R s (Y s) (P s)
        (M14HorizontalCovariantDerivative G R.curve C P EP s) Z = 0 := by
    obtain ⟨w, hw⟩ := exists_horizontalGauge_coordinates b (hrec s hs) Z
    have hDP := horizontalCovariantDerivative_lifted_gauge b hCoordinates W T x₀ hβ hrec
      hclock EP (fun r => (v r).2) hPcoord hs (uniqueDiffOn_Icc hac s hs)
    rw [horizontalJacobiPairResidual_gauge R b hCoordinates hscalar W hM04 x₀ hac hsub hβ
      hrec hclock hs (v s).1 (v s).2 _ w (hYcoord s hs) (hPcoord s hs) hDP hw]
    have hd : derivWithin (fun r => (v r).2) C s =
        M08.chartMetricDualInverse W.flow T x₀ (s, q s)
          (M08.closedChartJacobiPotential W.flow T x₀ C (s, q s) (derivWithin q C s) (v s).1 -
            M08.timeWithinFDeriv C (extChartAt (𝓡 n) x₀).target
              (M08.chartActionMetric W.flow T x₀) (s, q s) (v s).2) -
        M08.closedChartConnection W.flow T x₀ C (s, q s) (derivWithin q C s) (v s).2 :=
      ((ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℝ (Fin n))).hasFDerivAt.comp_hasDerivWithinAt s (hvd s hs)).derivWithin
          (uniqueDiffOn_Icc hac s hs)
    rw [hd, sub_add_cancel, M08.chartMetricDualInverse_pair W.flow T x₀ (hmem hs)]
    simp only [sub_apply]
    ring
  refine ⟨fun s => (Y s, P s), ⟨hac, hsub, hY, hP, EY, EP, hfirst, hsecond⟩, ?_⟩
  have hY₀ := hYcoord t₀ ht₀
  have hP₀ := hPcoord t₀ ht₀
  simp only [hv₀'] at hY₀ hP₀
  exact Prod.ext (eq_of_heq (hY₀.trans hv₀.symm)) (eq_of_heq (hP₀.trans hp₀.symm))

end PoincareConjecture.M14
