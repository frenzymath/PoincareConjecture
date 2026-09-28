import PoincareConjecture.Proofs.M14.Sec6_4_UnitAdaptedField
import PoincareConjecture.Proofs.M14.Sec6_4_ClosedAdaptedODE
import PoincareConjecture.Proofs.M14.Sec6_2_JacobiGaugeCoefficients
import PoincareConjecture.Proofs.M14.Sec6_2_JacobiGaugeCoordinates
import PoincareConjecture.Proofs.M14.Sec6_2_ClosedFieldExtension










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

private theorem horizontal_three_eval_heq
    (F : ∀ q, G.Horizontal q → G.Horizontal q → G.Horizontal q → ℝ)
    {q r : G.Point} (h : q = r)
    {P DP W : G.Horizontal q} {P' DP' W' : G.Horizontal r}
    (hP : HEq P P') (hDP : HEq DP DP') (hW : HEq W W') :
    F q P DP W = F r P' DP' W' := by
  cases h
  cases hP
  cases hDP
  cases hW
  rfl

variable {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  (R : M14SquareRootPath G p) (b : G.gaugeCover.index)




theorem exists_gaugeHorizontalUnitAdaptedField
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (hM04 : RicciFlowCurvatureTheory.{0}) (x₀ : G.gaugeCover.spatial b)
    {a c t₀ : ℝ} (hac : a < c) (hsub : Icc a c ⊆ M14SqrtParameterInterval τ₁ τ₂)
    {β : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b}
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β (Icc a c))
    (hrec : ∀ s ∈ Icc a c, (G.gaugeCover.cylinder b).toSpacetime (β s) = R.curve s)
    (hclock : ∀ s ∈ Icc a c, (β s).1.val = T - s ^ 2)
    (ht₀ : t₀ ∈ Icc a c) (P₀ : G.Horizontal (R.curve t₀)) :
    ∃ P : ∀ s, G.Horizontal (R.curve s),
      IsHorizontalUnitAdaptedFieldOn R a c P ∧ P t₀ = P₀ := by
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
  obtain ⟨v₀, hv₀⟩ := exists_horizontalGauge_coordinates b (hrec t₀ ht₀) P₀
  obtain ⟨v, hv₀', hv, hvd⟩ := exists_closedCoordinateAdapted_solution W.flow T x₀
    hac htime hq hmem ht₀ v₀
  let P := horizontalFieldOfGauge b hrec v
  have hP := horizontalFieldOfGauge_contMDiffOn b hβ hrec hv
  obtain ⟨E⟩ := exists_pullbackExtension_Icc hac hP
  have hPcoord := fun s hs => horizontalFieldOfGauge_heq b hrec v (s := s) hs
  have hpaired (s : ℝ) (hs : s ∈ C) (Z : G.Horizontal (R.curve s)) :
      G.spacetime.horizontalMetric.inner (R.curve s)
        (M14HorizontalCovariantDerivative G R.curve C P E s) Z =
          -(2 * s) * horizontalRicci G.leafwise (R.curve s) (P s) Z := by
    obtain ⟨w, hw⟩ := exists_horizontalGauge_coordinates b (hrec s hs) Z
    have hDP := horizontalCovariantDerivative_lifted_gauge b hCoordinates W T x₀ hβ hrec
      hclock E v hPcoord hs (uniqueDiffOn_Icc hac s hs)
    let d := derivWithin v C s + M08.closedChartConnection W.flow T x₀ C (s, q s)
      (derivWithin q C s) (v s)
    let φ := fun (z : G.Point) (P DP Z : G.Horizontal z) =>
      G.spacetime.horizontalMetric.inner z DP Z + 2 * s * horizontalRicci G.leafwise z P Z
    have hgeom := horizontal_three_eval_heq φ (hrec s hs).symm (hPcoord s hs) hDP hw
    have hmetric := gauge_chartActionMetric b W T x₀ (β s).2 s (β s).1
      (hclock s hs).symm d w
    have htimePair := gauge_chartActionMetric_timeWithin_pair b hCoordinates W hM04 T hac
      htime x₀ (β s).2 hs (β s).1 (hclock s hs).symm (v s) w
    have hd : derivWithin v C s =
        -M08.closedChartConnection W.flow T x₀ C (s, q s) (derivWithin q C s) (v s) -
          (1 / 2 : ℝ) • M08.chartMetricDualInverse W.flow T x₀ (s, q s)
            (M08.timeWithinFDeriv C (extChartAt (𝓡 n) x₀).target
              (M08.chartActionMetric W.flow T x₀) (s, q s) (v s)) := by
      exact (hvd s hs).derivWithin (uniqueDiffOn_Icc hac s hs)
    have hcoord : M08.chartActionMetric W.flow T x₀ (s, q s) d w +
        (1 / 2 : ℝ) * M08.timeWithinFDeriv C (extChartAt (𝓡 n) x₀).target
          (M08.chartActionMetric W.flow T x₀) (s, q s) (v s) w = 0 := by
      dsimp only [d]
      rw [hd]
      simp only [map_add, map_sub, map_neg, map_smul, add_apply, sub_apply, neg_apply,
        smul_apply, smul_eq_mul]
      rw [M08.chartMetricDualInverse_pair W.flow T x₀ (z := (s, q s)) (hmem hs)]
      ring
    change G.spacetime.horizontalMetric.inner (R.curve s)
        (M14HorizontalCovariantDerivative G R.curve C P E s) Z +
        2 * s * horizontalRicci G.leafwise (R.curve s) (P s) Z = _ at hgeom
    dsimp only [φ] at hgeom
    change _ = G.spacetime.horizontalMetric.inner _ _ _ at hmetric
    change M08.chartActionMetric W.flow T x₀ (s, q s) d w = _ at hmetric
    change M08.timeWithinFDeriv C (extChartAt (𝓡 n) x₀).target
      (M08.chartActionMetric W.flow T x₀) (s, q s) (v s) w = _ at htimePair
    linarith
  refine ⟨P, ⟨hac, hsub, hP, E, hpaired⟩, ?_⟩
  have hP₀ := hPcoord t₀ ht₀
  rw [hv₀'] at hP₀
  exact eq_of_heq (hP₀.trans hv₀.symm)

end PoincareConjecture.M14
