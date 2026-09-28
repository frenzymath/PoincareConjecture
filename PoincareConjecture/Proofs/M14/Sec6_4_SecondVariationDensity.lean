import PoincareConjecture.Proofs.M14.Sec6_4_VariationSurfaceTerms

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  {R : M14SquareRootPath G p}

theorem secondVariation_density_identity_with_residual
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (V : M14LVariationData G p R) (D : M14VariationDerivativeData V)
    {s : ℝ} (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    M08.variationParameterDeriv (M14SqrtParameterInterval τ₁ τ₂) V.parameterDomain
        (M08.variationParameterDeriv (M14SqrtParameterInterval τ₁ τ₂) V.parameterDomain
          (variationActionDensity V)) (s, 0) =
      derivWithin (variationAccelerationBoundaryPair V D) (M14SqrtParameterInterval τ₁ τ₂) s +
        M14SecondVariationIndexDensity V D s -
        M14SquareRootEulerResidual G R D.base_extension s (variationAccelerationField V D s) := by
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  have hscalar := ((hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise).scalar_smooth
  have hsC : s ∈ M14SqrtParameterInterval τ₁ τ₂ := Ioo_subset_Icc_self hs
  obtain ⟨b, N, P, β, hN, hsN, hP, hzero, hPsub, hβ, hrec, hclock⟩ :=
    exists_variation_gauge_rectangle V hsC
  obtain ⟨W⟩ := ordinaryGaugeWitness_nonempty b hCoordinates
  let C := M14SqrtParameterInterval τ₁ τ₂
  let S := C ∩ N
  let J := Ioo (Real.sqrt τ₁) (Real.sqrt τ₂) ∩ N
  let x₀ := (β (s, 0)).2
  let e := extChartAt (𝓡 n) x₀
  let U := e.target
  let O := J ×ˢ U
  let Ω := J ×ˢ P
  let q := fun z : ℝ × ℝ => (β z).2.val
  let m := M08.chartActionMetric W.flow T x₀
  let P₀ := M08.chartActionPotential W.flow T x₀
  let Γ := M08.closedChartConnection W.flow T x₀ S
  have hC : UniqueDiffOn ℝ C := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)
  have hS : UniqueDiffOn ℝ S := hC.inter hN
  have hJ : IsOpen J := isOpen_Ioo.inter hN
  have hU : IsOpen U := isOpen_extChartAt_target (I := 𝓡 n) x₀
  have hO : IsOpen O := hJ.prod hU
  have hΩ : IsOpen Ω := hJ.prod hP
  have hp : (s, (0 : ℝ)) ∈ Ω := ⟨⟨hs, hsN⟩, hzero⟩
  have htime (r : ℝ) (hr : r ∈ S) : T - r ^ 2 ∈ (G.gaugeCover.interval b).domain := by
    rw [← hclock r hr 0 hzero]
    exact (β (r, 0)).1.property
  have hsub : O ⊆ S ×ˢ U := fun _ hz => ⟨⟨Ioo_subset_Icc_self hz.1.1, hz.1.2⟩, hz.2⟩
  have hm : ContDiffOn ℝ ∞ m O :=
    (M08.chartActionMetric_closed_contDiffOn W.flow T x₀ htime).mono hsub
  have hP₀ : ContDiffOn ℝ ∞ P₀ O :=
    (M08.chartActionPotential_closed_contDiffOn W.flow hM04 T x₀ htime).mono hsub
  have hΓ : ContDiffOn ℝ ∞ Γ O :=
    (M08.closedChartConnection_contDiffOn W.flow T x₀ hS htime).mono hsub
  have hq : ContDiffOn ℝ ∞ q Ω := (variationGauge_spatial_contDiffOn b hβ).mono
    (fun _ hz => ⟨⟨Ioo_subset_Icc_self hz.1.1, hz.1.2⟩, hz.2⟩)
  have hmap : MapsTo (fun z => (z.1, q z)) Ω O := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    have hsrc : (β z).2 ∈ e.source := by
      rw [extChartAt_source, (G.gaugeCover.spatial b).chartAt_source_eq_univ]
      exact mem_univ _
    have heq : e (β z).2 = q z := by
      rw [extChartAt_coe]
      rfl
    change q z ∈ e.target
    rw [← heq]
    exact e.map_source hsrc
  have hsym (z : ℝ × EuclideanSpace ℝ (Fin n)) (hz : z ∈ O)
      (v w : EuclideanSpace ℝ (Fin n)) : m z v w = m z w v := by
    obtain ⟨r, a⟩ := z
    have hy : e.symm a ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x₀).source := by
      simpa only [e, extChartAt_source] using e.map_target hz.2
    have heq : extChartAt (𝓡 n) x₀ (e.symm a) = a := e.right_inv hz.2
    simpa only [heq] using M08.chartActionMetric_symm_at W.flow T hy r v w
  have hcompat (z : ℝ × EuclideanSpace ℝ (Fin n)) (hz : z ∈ O)
      (a v w : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun y => m (z.1, y)) z.2 a v w =
        m z (Γ z a v) w + m z v (Γ z a w) := by
    obtain ⟨r, y⟩ := z
    have hy : e.symm y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x₀).source := by
      simpa only [e, extChartAt_source] using e.map_target hz.2
    have heq : extChartAt (𝓡 n) x₀ (e.symm y) = y := e.right_inv hz.2
    simpa only [heq] using M08.closedChartConnection_spatial_compatibility W.flow T htime hy
      ⟨Ioo_subset_Icc_self hz.1.1, hz.1.2⟩ a v w
  have htor (z : ℝ × EuclideanSpace ℝ (Fin n)) (hz : z ∈ O)
      (v w : EuclideanSpace ℝ (Fin n)) : Γ z v w = Γ z w v := by
    obtain ⟨r, y⟩ := z
    have hy : e.symm y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x₀).source := by
      simpa only [e, extChartAt_source] using e.map_target hz.2
    have heq : extChartAt (𝓡 n) x₀ (e.symm y) = y := e.right_inv hz.2
    change M08.closedChartChristoffel W.flow T x₀ S (r, y) v w =
      M08.closedChartChristoffel W.flow T x₀ S (r, y) w v
    simpa only [heq] using M08.closedChartChristoffel_symm W.flow T htime hy
      ⟨Ioo_subset_Icc_self hz.1.1, hz.1.2⟩ v w
  have hid := M08.surfaceActionDensity_second_boundary hΩ hO m P₀ Γ q hm hP₀ hΓ hq hmap
    hsym hcompat htor hp
  dsimp only at hid
  rw [surfaceIndex_gauge V D b hCoordinates hscalar hM04 W x₀ hN hP hzero hβ hrec hclock hs hsN,
    surfaceEuler_gauge V D b hCoordinates hscalar hM04 W x₀ hN hP hzero hβ hrec hclock
      hPsub hs hsN] at hid
  have hLnear : (fun u => variationActionDensity V (s, u)) =ᶠ[𝓝 (0 : ℝ)]
      (fun u => M08.surfaceActionDensity m P₀ q (s, u)) := by
    filter_upwards [hP.mem_nhds hzero] with u hu
    exact (surfaceActionDensity_gauge V b hCoordinates W x₀ hN hP hβ hrec hclock hs hsN hu).symm
  have hPV : IsOpen V.parameterDomain := V.parameterDomain_eq ▸ isOpen_Ioo
  have hzeroV : (0 : ℝ) ∈ V.parameterDomain := hPsub hzero
  have hL := variationActionDensity_contDiffOn hM12 V
  have hL' := M08.variationParameterDeriv_contDiffOn hC hPV _ hL
  have hfirst : (fun u => M08.variationParameterDeriv C V.parameterDomain
      (variationActionDensity V) (s, u)) =ᶠ[𝓝 (0 : ℝ)]
      (fun u => deriv (fun v => variationActionDensity V (s, v)) u) := by
    filter_upwards [hPV.mem_nhds hzeroV] with u hu
    exact (M08.hasDerivAt_variationParameter hPV _ hL hsC hu).deriv.symm
  have hraw := (M08.hasDerivAt_variationParameter hPV _ hL' hsC hzeroV).deriv.symm
  have hraw' := (hraw.trans hfirst.deriv_eq).trans hLnear.deriv.deriv_eq
  have hBnear : (fun r => M08.surfaceAccelerationBoundaryPair m Γ q (r, 0)) =ᶠ[𝓝 s]
      variationAccelerationBoundaryPair V D := by
    filter_upwards [hJ.mem_nhds ⟨hs, hsN⟩] with r hr
    exact surfaceAccelerationBoundaryPair_gauge V b hCoordinates W x₀ hN hP hβ hrec hclock
      D hzero hPsub hr.1 hr.2
  rw [hBnear.deriv_eq, ← derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)] at hid
  exact hraw'.trans hid

end PoincareConjecture.M14
