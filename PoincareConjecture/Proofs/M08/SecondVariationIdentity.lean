import PoincareConjecture.Proofs.M08.VariationSurfaceBridge

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option maxHeartbeats 2600000 in
theorem secondVariation_density_identity {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    {p : BackwardTimePath F T τ₁ τ₂} (V : LVariation F T τ₁ τ₂ p)
    (D : LVariationDerivativeData V) (R : RegularizedLGeodesicData p) {s : ℝ}
    (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    variationParameterDeriv (sqrtParameterInterval τ₁ τ₂) V.parameterDomain
        (variationParameterDeriv (sqrtParameterInterval τ₁ τ₂) V.parameterDomain
          (variationActionDensity V)) (s, 0) =
      derivWithin (variationAccelerationBoundaryPair V D) (sqrtParameterInterval τ₁ τ₂) s +
        secondVariationIndexDensity V D s := by
  let C := sqrtParameterInterval τ₁ τ₂
  let I := Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)
  let x := V.baseSquareCurve s
  let e := extChartAt (𝓡 n) x
  let U := e.target
  let O := I ×ˢ U
  let Ω := variationChartDomain V x ∩ Prod.fst ⁻¹' I
  let G := chartActionMetric F T x
  let P := chartActionPotential F T x
  let Γ := closedChartConnection F T x C
  let q := variationChart V x
  have hC : UniqueDiffOn ℝ C := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.nonnegative p.ordered)
  have hsC : s ∈ C := Ioo_subset_Icc_self hs
  have hsN : C ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
  have htime (r : ℝ) (hr : r ∈ C) : T - r ^ 2 ∈ J :=
    p.time_mem _ (square_mem_backward_interval p hr)
  have hU : IsOpen U := isOpen_extChartAt_target (I := 𝓡 n) x
  have hO : IsOpen O := isOpen_Ioo.prod hU
  have hΩ : IsOpen Ω := (variationChartDomain_open V x).inter
    (isOpen_Ioo.preimage continuous_fst)
  have hzero : (0 : ℝ) ∈ V.parameterDomain := ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  have hx : V.baseSquareCurve s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source :=
    mem_chart_source _ _
  have hsΩ : (s, (0 : ℝ)) ∈ Ω := ⟨⟨V.square_contains ⟨hsC, hzero⟩, hx⟩, hs⟩
  have hsub : O ⊆ C ×ˢ U := prod_mono Ioo_subset_Icc_self Subset.rfl
  have hG : ContDiffOn ℝ ∞ G O := (chartActionMetric_closed_contDiffOn F T x htime).mono hsub
  have hP : ContDiffOn ℝ ∞ P O := (chartActionPotential_closed_contDiffOn F hM04 T x htime).mono hsub
  have hΓ : ContDiffOn ℝ ∞ Γ O := (closedChartConnection_contDiffOn F T x hC htime).mono hsub
  have hq : ContDiffOn ℝ ∞ q Ω := (variationChart_contDiffOn V x).mono inter_subset_left
  have hmap : MapsTo (fun z ↦ (z.1, q z)) Ω O := by
    intro z hz
    refine ⟨hz.2, e.map_source ?_⟩
    have hsrc : V.squareFamily z.1 z.2 ∈
        (chartAt (EuclideanSpace ℝ (Fin n)) x).source := hz.1.2
    simpa only [e, extChartAt_source] using hsrc
  have hsym (z : ℝ × EuclideanSpace ℝ (Fin n)) (hz : z ∈ O)
      (v w : EuclideanSpace ℝ (Fin n)) : G z v w = G z w v := by
    obtain ⟨r, a⟩ := z
    have hy : e.symm a ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
      simpa only [e, extChartAt_source] using e.map_target hz.2
    have he : extChartAt (𝓡 n) x (e.symm a) = a := e.right_inv hz.2
    simpa only [he] using chartActionMetric_symm_at F T hy r v w
  have hcompat (z : ℝ × EuclideanSpace ℝ (Fin n)) (hz : z ∈ O)
      (y v w : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun a ↦ G (z.1, a)) z.2 y v w = G z (Γ z y v) w + G z v (Γ z y w) := by
    obtain ⟨r, a⟩ := z
    have hy : e.symm a ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
      simpa only [e, extChartAt_source] using e.map_target hz.2
    have he : extChartAt (𝓡 n) x (e.symm a) = a := e.right_inv hz.2
    simpa only [he] using closedChartConnection_spatial_compatibility F T htime hy
      (Ioo_subset_Icc_self hz.1) y v w
  have htor (z : ℝ × EuclideanSpace ℝ (Fin n)) (hz : z ∈ O)
      (v w : EuclideanSpace ℝ (Fin n)) : Γ z v w = Γ z w v := by
    obtain ⟨r, a⟩ := z
    have hy : e.symm a ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
      simpa only [e, extChartAt_source] using e.map_target hz.2
    have he : extChartAt (𝓡 n) x (e.symm a) = a := e.right_inv hz.2
    change closedChartChristoffel F T x C (r, a) v w =
      closedChartChristoffel F T x C (r, a) w v
    simpa only [he] using closedChartChristoffel_symm F T htime hy
      (Ioo_subset_Icc_self hz.1) v w
  have hid := surfaceActionDensity_second_boundary hΩ hO G P Γ q hG hP hΓ hq hmap
    hsym hcompat htor hsΩ
  dsimp only at hid
  rw [surfaceIndex_variationChart hM04 V D hs hx,
    surfaceEuler_variationChart hM04 V D hs hx,
    variation_regularizedEulerResidual_zero V D R hsC, sub_zero] at hid
  have hnearU : ∀ᶠ u in 𝓝 (0 : ℝ), (s, u) ∈ Ω :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hΩ.mem_nhds hsΩ)
  have hLnear : (fun u ↦ variationActionDensity V (s, u)) =ᶠ[𝓝 (0 : ℝ)]
      (fun u ↦ surfaceActionDensity G P q (s, u)) := by
    filter_upwards [hnearU] with u hu
    exact (surfaceActionDensity_variationChart V hu.1).symm
  have hL := variationActionDensity_contDiffOn hM04 V
  have hL' := variationParameterDeriv_contDiffOn hC isOpen_Ioo _ hL
  have hfirst : (fun u ↦ variationParameterDeriv C V.parameterDomain
      (variationActionDensity V) (s, u)) =ᶠ[𝓝 (0 : ℝ)]
      (fun u ↦ deriv (fun v ↦ variationActionDensity V (s, v)) u) := by
    filter_upwards [isOpen_Ioo.mem_nhds hzero] with u hu
    exact (hasDerivAt_variationParameter isOpen_Ioo _ hL hsC hu).deriv.symm
  have hraw := (hasDerivAt_variationParameter isOpen_Ioo _ hL' hsC hzero).deriv.symm
  have hraw' := (hraw.trans hfirst.deriv_eq).trans hLnear.deriv.deriv_eq
  have hnearS : ∀ᶠ r in 𝓝 s, (r, (0 : ℝ)) ∈ Ω :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hΩ.mem_nhds hsΩ)
  have hBnear : (fun r ↦ surfaceAccelerationBoundaryPair G Γ q (r, 0)) =ᶠ[𝓝 s]
      variationAccelerationBoundaryPair V D := by
    filter_upwards [hnearS] with r hr
    exact surfaceAccelerationBoundaryPair_variationChart V D (Ioo_subset_Icc_self hr.2) hr.1.2
  rw [hBnear.deriv_eq, ← derivWithin_of_mem_nhds hsN] at hid
  exact hraw'.trans hid

end PoincareConjecture.M08
