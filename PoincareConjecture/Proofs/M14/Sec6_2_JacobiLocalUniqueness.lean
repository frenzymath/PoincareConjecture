import PoincareConjecture.Proofs.M14.Sec6_2_JacobiLocalExistence










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p} (b : G.gaugeCover.index)
  (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
  (hscalar : ContMDiff (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
    (horizontalScalarCurvature G.leafwise))
  (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
  (hM04 : RicciFlowCurvatureTheory.{0}) (x₀ : G.gaugeCover.spatial b)
  {a c : ℝ}
  {β : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b}
  (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β (Icc a c))
  (hrec : ∀ s ∈ Icc a c, (G.gaugeCover.cylinder b).toSpacetime (β s) = R.curve s)
  (hclock : ∀ s ∈ Icc a c, (β s).1.val = T - s ^ 2)

include hCoordinates hscalar W hM04 x₀ hβ hrec hclock




theorem IsHorizontalJacobiPairOn.coordinate_phase
    {z : ∀ s, G.Horizontal (R.curve s) × G.Horizontal (R.curve s)}
    (hz : IsHorizontalJacobiPairOn R a c z)
    (f g : ℝ → EuclideanSpace ℝ (Fin n))
    (hf : ContDiffOn ℝ ∞ f (Icc a c)) (hg : ContDiffOn ℝ ∞ g (Icc a c))
    (hY : ∀ s ∈ Icc a c,
      HEq (z s).1 ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2 (f s)))
    (hP : ∀ s ∈ Icc a c,
      HEq (z s).2 ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2 (g s))) :
    ∀ s ∈ Icc a c, HasDerivWithinAt (fun r => (f r, g r))
      (closedCoordinateJacobiPhase W.flow T x₀ (Icc a c)
        (fun r => (β r).2.val) s (f s, g s)) (Icc a c) s := by
  obtain ⟨EY, EP, hfirst, hsecond⟩ := hz.equations
  intro s hs
  let C := Icc a c
  let q := fun r => (β r).2.val
  let A := derivWithin q C s
  let j : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (β s)) :=
    (G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2
  have hDY := horizontalCovariantDerivative_lifted_gauge b hCoordinates W T x₀ hβ hrec
    hclock EY f hY hs (uniqueDiffOn_Icc hz.ordered s hs)
  rw [hfirst s hs] at hDY
  have hdf : derivWithin f C s =
      g s - M08.closedChartConnection W.flow T x₀ C (s, q s) A (f s) := by
    apply eq_sub_iff_add_eq.mpr
    exact j.injective (eq_of_heq (hDY.symm.trans (hP s hs)))
  have hDP := horizontalCovariantDerivative_lifted_gauge b hCoordinates W T x₀ hβ hrec
    hclock EP g hP hs (uniqueDiffOn_Icc hz.ordered s hs)
  have hdp (w : EuclideanSpace ℝ (Fin n)) :
      M08.chartActionMetric W.flow T x₀ (s, q s)
        (derivWithin g C s + M08.closedChartConnection W.flow T x₀ C (s, q s) A (g s)) w =
      M08.closedChartJacobiPotential W.flow T x₀ C (s, q s) A (f s) w -
        M08.timeWithinFDeriv C (extChartAt (𝓡 n) x₀).target
          (M08.chartActionMetric W.flow T x₀) (s, q s) (g s) w := by
    let Z := horizontalFieldOfGauge b hrec (fun _ => w) s
    have hZ := horizontalFieldOfGauge_heq b hrec (fun _ => w) hs
    have hres := hsecond s hs Z
    rw [horizontalJacobiPairResidual_gauge R b hCoordinates hscalar W hM04 x₀ hz.ordered
      hz.interval_subset hβ hrec hclock hs (f s) (g s) _ w (hY s hs) (hP s hs) hDP hZ] at hres
    linarith
  have hmem : q s ∈ (extChartAt (𝓡 n) x₀).target := by
    have hsrc : (β s).2 ∈ (extChartAt (𝓡 n) x₀).source := by
      rw [extChartAt_source, (G.gaugeCover.spatial b).chartAt_source_eq_univ]
      exact mem_univ _
    have he : extChartAt (𝓡 n) x₀ (β s).2 = (β s).2.val := by
      rw [extChartAt_coe]
      rfl
    simpa only [he] using (extChartAt (𝓡 n) x₀).map_source hsrc
  have heq := M08.covariantLinearPhaseOperator_eq_of_pair
    (M08.chartMetricDualInverse W.flow T x₀ (s, q s))
    (M08.chartActionMetric W.flow T x₀ (s, q s))
    (fun v => M08.chartMetricDualInverse_left W.flow T x₀ hmem v)
    (M08.closedChartConnection W.flow T x₀ C (s, q s) A)
    (M08.closedChartJacobiPotential W.flow T x₀ C (s, q s) A)
    (M08.timeWithinFDeriv C (extChartAt (𝓡 n) x₀).target
      (M08.chartActionMetric W.flow T x₀) (s, q s))
    (f s) (g s) (derivWithin f C s) (derivWithin g C s) hdf hdp
  have hd := ((hf s hs).differentiableWithinAt (by simp)).hasDerivWithinAt.prodMk
    ((hg s hs).differentiableWithinAt (by simp)).hasDerivWithinAt
  exact heq ▸ hd




theorem gaugeHorizontalJacobiPair_unique
    {z z' : ∀ s, G.Horizontal (R.curve s) × G.Horizontal (R.curve s)}
    (hz : IsHorizontalJacobiPairOn R a c z) (hz' : IsHorizontalJacobiPairOn R a c z')
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc a c) (hinit : z t₀ = z' t₀) :
    ∀ s ∈ Icc a c, z s = z' s := by
  obtain ⟨f, hf, hY⟩ := exists_smooth_horizontalGauge_coordinates b hβ hrec
    (fun s => (z s).1) hz.first_smooth
  obtain ⟨g, hg, hP⟩ := exists_smooth_horizontalGauge_coordinates b hβ hrec
    (fun s => (z s).2) hz.second_smooth
  obtain ⟨f', hf', hY'⟩ := exists_smooth_horizontalGauge_coordinates b hβ hrec
    (fun s => (z' s).1) hz'.first_smooth
  obtain ⟨g', hg', hP'⟩ := exists_smooth_horizontalGauge_coordinates b hβ hrec
    (fun s => (z' s).2) hz'.second_smooth
  have htime (s : ℝ) (hs : s ∈ Icc a c) : T - s ^ 2 ∈ (G.gaugeCover.interval b).domain := by
    rw [← hclock s hs]
    exact (β s).1.property
  have hmem : MapsTo (fun s => (β s).2.val) (Icc a c) (extChartAt (𝓡 n) x₀).target := by
    intro s hs
    have hsrc : (β s).2 ∈ (extChartAt (𝓡 n) x₀).source := by
      rw [extChartAt_source, (G.gaugeCover.spatial b).chartAt_source_eq_univ]
      exact mem_univ _
    have he : extChartAt (𝓡 n) x₀ (β s).2 = (β s).2.val := by
      rw [extChartAt_coe]
      rfl
    simpa only [he] using (extChartAt (𝓡 n) x₀).map_source hsrc
  let j₀ := (G.gaugeCover.metric b).spatialTangentEquiv (β t₀).1 (β t₀).2
  have hf₀ : f t₀ = f' t₀ := j₀.injective (eq_of_heq ((hY t₀ ht₀).symm.trans
    ((heq_of_eq (congrArg Prod.fst hinit)).trans (hY' t₀ ht₀))))
  have hg₀ : g t₀ = g' t₀ := j₀.injective (eq_of_heq ((hP t₀ ht₀).symm.trans
    ((heq_of_eq (congrArg Prod.snd hinit)).trans (hP' t₀ ht₀))))
  have heq := closedCoordinateJacobi_solution_unique W.flow T x₀ hM04 hz.ordered htime
    (gaugeLift_spatialCurve_contDiffOn b hβ) hmem ht₀
    (IsHorizontalJacobiPairOn.coordinate_phase b hCoordinates hscalar W hM04 x₀ hβ hrec hclock
      hz f g hf hg hY hP)
    (IsHorizontalJacobiPairOn.coordinate_phase b hCoordinates hscalar W hM04 x₀ hβ hrec hclock
      hz' f' g' hf' hg' hY' hP') (Prod.ext hf₀ hg₀)
  intro s hs
  let j : EuclideanSpace ℝ (Fin n) ≃L[ℝ]
      G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (β s)) :=
    (G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2
  exact Prod.ext
    (eq_of_heq ((hY s hs).trans ((heq_of_eq (congrArg j (congrArg Prod.fst (heq hs)))).trans
      (hY' s hs).symm)))
    (eq_of_heq ((hP s hs).trans ((heq_of_eq (congrArg j (congrArg Prod.snd (heq hs)))).trans
      (hP' s hs).symm)))

end PoincareConjecture.M14
