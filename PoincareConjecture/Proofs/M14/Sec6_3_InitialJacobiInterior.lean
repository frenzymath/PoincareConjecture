import PoincareConjecture.Proofs.M14.Sec6_3_InitialJacobiData
import PoincareConjecture.Proofs.M14.Sec6_3_InitialGaugePhase
import PoincareConjecture.Proofs.M14.Sec6_3_CoordinateFamilyJacobi
import PoincareConjecture.Proofs.M14.Sec6_3_JacobiGaugeSecond
import PoincareConjecture.Proofs.M14.Sec6_3_GaugeParameterDifferential
import PoincareConjecture.Proofs.M14.Sec6_3_GaugeFamilyNeighborhood

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x y : G.Point} {Z : G.Horizontal x}

private theorem horizontal_t2Space : T2Space (G.Horizontal x) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x

attribute [local instance] horizontal_t2Space

theorem initialValuePath_differential_jacobi_interior
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (P : M14SquareRootInitialValuePath G T τ x y Z) (W : G.Horizontal x)
    {s : ℝ} (hs : s ∈ Ioo 0 (Real.sqrt τ)) (V : G.Horizontal (P.square_path.curve s)) :
    M14JacobiResidual G P.square_path (initialValuePath_differentialData hM04 hM12 P W)
      s V = 0 := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  let S := Real.sqrt τ
  have hS : 0 < S := Real.sqrt_pos.mpr P.path.tau_lt
  have hC : M14SqrtParameterInterval 0 τ = Icc 0 S := by
    simp only [M14SqrtParameterInterval, Real.sqrt_zero, S]
  have hbase : G.spacetime.timeFunction x = T := by
    simpa only [GeneralizedFlowSpacetime.timeFunction, sub_zero] using P.path.base_time
  have hsurv : (Z, S) ∈ initialValueDomain G T x := by
    refine Or.inr ⟨hS, y, ?_⟩
    rw [show S ^ 2 = τ from Real.sq_sqrt P.path.tau_lt.le]
    exact ⟨P⟩
  obtain ⟨U, hU, hZU, htube, hsm⟩ :=
    initialValueCurve_smooth_prefix hM04 hM12 hbase hS hsurv
  obtain ⟨b, N, hN, hZN, hNU, l, r, h0l, hls, hsr, hrS, hnear, β, hβ, hrec, hclock⟩ :=
    exists_smooth_gaugeFamily_neighborhood hU hZU hs.1 hs.2.le
      (fun z : G.Horizontal x × ℝ => initialValueCurve G T x z.1 z.2) hsm
  have hsr' : s < r := right_lt_of_Icc_mem_nhdsWithin hs.1.le hs.2 hnear
  have hlr : l < r := hls.trans hsr'
  have hsub : Icc l r ⊆ Icc 0 S := Icc_subset_Icc h0l.le hrS
  have hsubP : Icc l r ⊆ M14SqrtParameterInterval 0 τ := by rwa [hC]
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  have hscalar := ((hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise).scalar_smooth
  let F := Classical.choice (ordinaryGaugeWitness_nonempty b hCoordinates)
  let x₀ := (β (Z, s)).2
  have hβslice (A : G.Horizontal x) (hA : A ∈ N) :
      ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ (fun t => β (A, t)) (Icc l r) :=
    hβ.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn (fun _ ht => ⟨hA, ht⟩)
  have hcl (A : G.Horizontal x) (hA : A ∈ N) (t : ℝ) (ht : t ∈ Icc l r) :
      (β (A, t)).1.val = T - t ^ 2 :=
    (hclock (A, t) ⟨hA, ht⟩).trans (initialValueCurve_clock hbase (htube ⟨hNU hA, hsub ht⟩))
  have hrecP (t : ℝ) (ht : t ∈ Icc l r) :
      (G.gaugeCover.cylinder b).toSpacetime (β (Z, t)) = P.square_path.curve t :=
    (hrec (Z, t) ⟨hZN, ht⟩).trans (initialValueCurve_eqOn_square hM04 hM12 P (hsubP ht))
  let f : ℝ × G.Horizontal x → EuclideanSpace ℝ (Fin n) := fun z => (β (z.2, z.1)).2.val
  have hf : ContDiffOn ℝ ∞ f (Icc l r ×ˢ N) := by
    have hval : ContMDiff (𝓡 n) (𝓡 n) ∞
        (Subtype.val : G.gaugeCover.spatial b → EuclideanSpace ℝ (Fin n)) :=
      contMDiff_subtype_val
    have hq := hval.comp_contMDiffOn (fun z hz => (hβ z hz).snd)
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hq
    exact hq.contDiffOn.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn
      (fun _ hz => ⟨hz.2, hz.1⟩)
  have htarget (t : ℝ) (_ht : t ∈ Icc l r) (A : G.Horizontal x) (_hA : A ∈ N) :
      f (t, A) ∈ (extChartAt (𝓡 n) x₀).target := by
    have heq : extChartAt (𝓡 n) x₀ (β (A, t)).2 = f (t, A) := by
      rw [extChartAt_coe]
      rfl
    rw [← heq]
    apply (extChartAt (𝓡 n) x₀).map_source
    rw [extChartAt_source, (G.gaugeCover.spatial b).chartAt_source_eq_univ]
    exact mem_univ _
  let Y : ℝ → EuclideanSpace ℝ (Fin n) := fun t => fderiv ℝ (fun A => f (t, A)) Z W
  have hfield (t : ℝ) (ht : t ∈ Icc l r) :
      HEq ((initialValuePath_differentialData hM04 hM12 P W).field t)
        ((G.gaugeCover.metric b).spatialTangentEquiv (β (Z, t)).1 (β (Z, t)).2 (Y t)) := by
    have hp : ContMDiffOn (𝓘(ℝ, G.Horizontal x)) (spacetimeModel n) ∞
        (fun A => β (A, t)) N :=
      hβ.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun _ hA => ⟨hA, ht⟩)
    have hg : (fun A => initialValueCurve G T x A t) =ᶠ[𝓝 Z]
        (fun A => (G.gaugeCover.cylinder b).toSpacetime (β (A, t))) := by
      filter_upwards [hN.mem_nhds hZN] with A hA
      exact (hrec (A, t) ⟨hA, ht⟩).symm
    have hd := gaugeMap_projectedDifferential_congr b
      ((hp.contMDiffAt (hN.mem_nhds hZN)).mdifferentiableAt (by simp)) hg W
    exact (initialValuePath_differentialField_heq hM04 hM12 P W (hsubP ht)).trans hd
  obtain ⟨w, hw⟩ := exists_horizontalGauge_coordinates b (β := fun t => β (Z, t))
    (s := s) (hrecP s ⟨hls.le, hsr'.le⟩) V
  rw [jacobiResidual_gauge_secondOrder P.square_path b hCoordinates hscalar F hM04 x₀
    hlr hsubP (hβslice Z hZN) hrecP (hcl Z hZN)
    (initialValuePath_differentialData hM04 hM12 P W) Y hfield ⟨hls.le, hsr'.le⟩ w hw]
  apply closedCoordinateJacobi_of_parameterFamily F.flow T x₀ hM04 (uniqueDiffOn_Icc hlr)
    (fun t ht => by rw [← hcl Z hZN t ht]; exact (β (Z, t)).1.property)
    hN f hf htarget ⟨hls.le, hsr'.le⟩ (Icc_mem_nhds hls hsr') hZN W _ w
  intro A hA
  exact initialValueCurve_gauge_velocityPhase hM04 hM12 hS
    (htube ⟨hNU hA, hS.le, le_rfl⟩) b F x₀ hlr hsub (hβslice A hA)
    (fun t ht => hrec (A, t) ⟨hA, ht⟩) (hcl A hA) ⟨hls, hsr'⟩

end PoincareConjecture.M14
