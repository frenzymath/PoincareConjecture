import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.LGeometry
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.IndexForm.IndexRegularity
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Jacobi.JacobiGaugeResidual
import PoincareLib.Geometry.RicciFlow.Generalized.Gauge.Geometry

/-!
# Closed continuity of the actual Jacobi pairing

Morgan-Tian Proposition 6.13 and Lemma 6.14, pp. 110-112. The
closed compatible-gauge formula for the corrected Jacobi residual is
smooth for smooth actual fields. Relative closed neighborhoods retain
both endpoints, so the integrands in Green's identity are continuous
on the full interval without an open extension of the base curve.
-/

set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  (R : M14SquareRootPath G p)

/-- Smooth actual horizontal fields have a smooth corrected Jacobi
pairing on every closed compatible-gauge interval, Proposition 6.13
and Lemma 6.14, pp. 110-112. -/
theorem gaugeHorizontalJacobiPairResidual_contDiffOn (b : G.gaugeCover.index)
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (hscalar : ContMDiff (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      (horizontalScalarCurvature G.leafwise))
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (hM04 : RicciFlowCurvatureTheory.{0}) (x₀ : G.gaugeCover.spatial b)
    {a c : ℝ} (hac : a < c) (hsub : Icc a c ⊆ M14SqrtParameterInterval τ₁ τ₂)
    {β : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b}
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β (Icc a c))
    (hrec : ∀ s ∈ Icc a c, (G.gaugeCover.cylinder b).toSpacetime (β s) = R.curve s)
    (hclock : ∀ s ∈ Icc a c, (β s).1.val = T - s ^ 2)
    {Y P DP Z : ∀ s, G.Horizontal (R.curve s)}
    (hY : ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R.curve s) (Y s)) (Icc a c))
    (hP : ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R.curve s) (P s)) (Icc a c))
    (hDP : ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R.curve s) (DP s)) (Icc a c))
    (hZ : ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R.curve s) (Z s)) (Icc a c)) :
    ContDiffOn ℝ ∞ (fun s => horizontalJacobiPairResidual R s (Y s) (P s) (DP s) (Z s))
      (Icc a c) := by
  obtain ⟨f, hf, hfY⟩ := exists_smooth_horizontalGauge_coordinates b hβ hrec Y hY
  obtain ⟨g, hg, hgP⟩ := exists_smooth_horizontalGauge_coordinates b hβ hrec P hP
  obtain ⟨d, hd, hdDP⟩ := exists_smooth_horizontalGauge_coordinates b hβ hrec DP hDP
  obtain ⟨w, hw, hwZ⟩ := exists_smooth_horizontalGauge_coordinates b hβ hrec Z hZ
  let C := Icc a c
  let q := fun s => (β s).2.val
  have hC : UniqueDiffOn ℝ C := uniqueDiffOn_Icc hac
  have hq : ContDiffOn ℝ ∞ q C := gaugeLift_spatialCurve_contDiffOn b hβ
  have htime (s : ℝ) (hs : s ∈ C) : T - s ^ 2 ∈ (G.gaugeCover.interval b).domain := by
    rw [← hclock s hs]
    exact (β s).1.property
  have hpoint := contDiffOn_id.prodMk hq
  have hmap : MapsTo (fun s => (s, q s)) C (C ×ˢ (extChartAt (𝓡 n) x₀).target) := by
    intro s hs
    refine ⟨hs, ?_⟩
    have hsrc : (β s).2 ∈ (extChartAt (𝓡 n) x₀).source := by
      rw [extChartAt_source, (G.gaugeCover.spatial b).chartAt_source_eq_univ]
      exact mem_univ _
    have he : extChartAt (𝓡 n) x₀ (β s).2 = (β s).2.val := by
      rw [extChartAt_coe]
      rfl
    simpa only [he] using (extChartAt (𝓡 n) x₀).map_source hsrc
  have hA := hq.derivWithin hC (m := ∞) (by simp)
  have hG := (M08.chartActionMetric_closed_contDiffOn W.flow T x₀ htime).comp hpoint hmap
  have hV := (M08.closedChartJacobiPotential_contDiffOn W.flow hM04 T x₀ hC htime).comp
    (hpoint.prodMk hA) (fun s hs => ⟨hmap hs, mem_univ _⟩)
  have hH := (M08.timeWithinFDeriv_contDiffOn hC (isOpen_extChartAt_target (I := 𝓡 n) x₀)
    (M08.chartActionMetric W.flow T x₀)
    (M08.chartActionMetric_closed_contDiffOn W.flow T x₀ htime)).comp hpoint hmap
  apply ((((hG.clm_apply hd).clm_apply hw).sub ((hV.clm_apply hf).clm_apply hw)).add
    ((hH.clm_apply hg).clm_apply hw)).congr
  intro s hs
  exact horizontalJacobiPairResidual_gauge R b hCoordinates hscalar W hM04 x₀ hac hsub
    hβ hrec hclock hs (f s) (g s) (d s) (w s) (hfY s hs) (hgP s hs) (hdDP s hs) (hwZ s hs)

/-- The corrected actual Jacobi pairing is smooth on the entire
closed square interval for smooth horizontal arguments, including
both endpoints, Proposition 6.13 and Lemma 6.14, pp. 110-112. -/
theorem horizontalJacobiPairResidual_contDiffOn
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {Y P DP Z : ∀ s, G.Horizontal (R.curve s)}
    (hY : ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R.curve s) (Y s))
        (M14SqrtParameterInterval τ₁ τ₂))
    (hP : ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R.curve s) (P s))
        (M14SqrtParameterInterval τ₁ τ₂))
    (hDP : ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R.curve s) (DP s))
        (M14SqrtParameterInterval τ₁ τ₂))
    (hZ : ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (R.curve s) (Z s))
        (M14SqrtParameterInterval τ₁ τ₂)) :
    ContDiffOn ℝ ∞ (fun s => horizontalJacobiPairResidual R s (Y s) (P s) (DP s) (Z s))
      (M14SqrtParameterInterval τ₁ τ₂) := by
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  have hscalar := ((hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise).scalar_smooth
  intro s hs
  obtain ⟨b, N, β, hN, hsN, hβ, hrec, hclock⟩ := exists_squareRoot_gauge_neighborhood R hs
  have hab := Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt
  obtain ⟨l, r, hal, hlr, hrb, hls, hsr, hsubN, hnear⟩ :=
    M08.exists_enlarged_closed_interval hab hs.1 le_rfl hs.2 hN
      (by simpa only [Icc_self, singleton_subset_iff] using hsN)
  have hsub : Icc l r ⊆ M14SqrtParameterInterval τ₁ τ₂ := Icc_subset_Icc hal hrb
  have hsub' : Icc l r ⊆ M14SqrtParameterInterval τ₁ τ₂ ∩ N :=
    fun _ hv => ⟨hsub hv, hsubN hv⟩
  obtain ⟨W⟩ := ordinaryGaugeWitness_nonempty b hCoordinates
  have hlocal := gaugeHorizontalJacobiPairResidual_contDiffOn R b hCoordinates hscalar W hM04
    (β s).2 hlr hsub (hβ.mono hsub') (fun v hv => hrec v (hsub' hv))
    (fun v hv => hclock v (hsub' hv)) (hY.mono hsub) (hP.mono hsub) (hDP.mono hsub)
    (hZ.mono hsub)
  exact (hlocal s ⟨hls, hsr⟩).mono_of_mem_nhdsWithin (hnear s ⟨le_rfl, le_rfl⟩)

end PoincareMT.M14
