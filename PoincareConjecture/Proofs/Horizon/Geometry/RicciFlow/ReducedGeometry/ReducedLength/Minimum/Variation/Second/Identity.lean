import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Intrinsic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Compatibility
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.CoefficientRegularity









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

open ReducedLengthMinimum.Variational

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

local instance secondDualGroup : NormedAddCommGroup (EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondDualSpace : NormedSpace ℝ (EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
local instance secondBilinearGroup : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance secondBilinearSpace : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

set_option maxHeartbeats 2600000 in
theorem secondVariation_density_identity {J : Set ℝ} {F : RicciFlow 2 M J}
    {T τ₁ τ₂ : ℝ}
    (hpotential : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => 2 * z.1 ^ 2 *
        (F.connection (T - z.1 ^ 2)).scalarCurvature z.2))
    (htime : ∀ r ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂), T - r ^ 2 ∈ interior J)
    {p : BackwardTimePath F T τ₁ τ₂} (V : LVariation F T τ₁ τ₂ p)
    (D : LVariationDerivativeData V)
    (heuler : ∀ r ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂),
      ∀ W : TangentSpace (𝓡 2) (V.baseSquareCurve r),
        regularizedEulerResidual F T V.baseSquareCurve
          (sqrtParameterInterval τ₁ τ₂) D.velocity_extension r W = 0) {s : ℝ}
    (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    variationParameterDeriv (sqrtParameterInterval τ₁ τ₂) V.parameterDomain
        (variationParameterDeriv (sqrtParameterInterval τ₁ τ₂) V.parameterDomain
          (variationActionDensity V)) (s, 0) =
      derivWithin (variationAccelerationBoundaryPair V D) (sqrtParameterInterval τ₁ τ₂) s +
        secondVariationIndexDensity V D s := by
  let C := sqrtParameterInterval τ₁ τ₂
  let I := Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)
  let x := V.baseSquareCurve s
  let e := extChartAt (𝓡 2) x
  let U := e.target
  let O := chartActionDomain F T x
  let Ω := variationChartDomain V x ∩ Prod.fst ⁻¹' I
  let G := chartActionMetric F T x
  let P := chartActionPotential F T x
  let Γ := Frame.chartConnectionBilinear G
  let q := variationChart V x
  have hC : UniqueDiffOn ℝ C := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.nonnegative p.ordered)
  have hsC : s ∈ C := Ioo_subset_Icc_self hs
  have hsN : C ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
  have hO : IsOpen O := chartActionDomain_open F T x
  have hΩ : IsOpen Ω := (variationChartDomain_open V x).inter
    (isOpen_Ioo.preimage continuous_fst)
  have hzero : (0 : ℝ) ∈ V.parameterDomain := ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  have hx : V.baseSquareCurve s ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) x).source :=
    mem_chart_source _ _
  have hsΩ : (s, (0 : ℝ)) ∈ Ω := ⟨⟨V.square_contains ⟨hsC, hzero⟩, hx⟩, hs⟩
  have hG : ContDiffOn ℝ ∞ G O := chartActionMetric_contDiffOn F T x
  have hP : ContDiffOn ℝ ∞ P O := chartActionPotential_contDiffOn F T hpotential x
  have hpos : ∀ z ∈ O, ∀ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 → 0 < G z v v :=
    fun z hz ↦ chartActionMetric_pos F T x hz
  have hΓ : ContDiffOn ℝ ∞ Γ O :=
    Frame.chartConnectionBilinear_contDiffOn G O hO hG hpos
  have hq : ContDiffOn ℝ ∞ q Ω := (variationChart_contDiffOn V x).mono inter_subset_left
  have hmap : MapsTo (fun z ↦ (z.1, q z)) Ω O := by
    intro z hz
    refine ⟨squareTime_mem_interior_preimage (htime z.1 hz.2), e.map_source ?_⟩
    have hsrc : V.squareFamily z.1 z.2 ∈
        (chartAt (EuclideanSpace ℝ (Fin 2)) x).source := hz.1.2
    simpa only [e, extChartAt_source] using hsrc
  have hsym (z : ℝ × EuclideanSpace ℝ (Fin 2)) (hz : z ∈ O)
      (v w : EuclideanSpace ℝ (Fin 2)) : G z v w = G z w v :=
    chartActionMetric_symm F T x hz v w
  have hsymNear (z : ℝ × EuclideanSpace ℝ (Fin 2)) (hz : z ∈ O) :
      ∀ᶠ q in 𝓝 z, ∀ v w, G q v w = G q w v := by
    filter_upwards [hO.mem_nhds hz] with q hq
    exact hsym q hq
  have hcompat (z : ℝ × EuclideanSpace ℝ (Fin 2)) (hz : z ∈ O)
      (y v w : EuclideanSpace ℝ (Fin 2)) :
      fderiv ℝ (fun a ↦ G (z.1, a)) z.2 y v w = G z (Γ z y v) w + G z v (Γ z y w) := by
    rw [(hasFDerivAt_spatial hO G hG hz).fderiv]
    exact Frame.chartConnection_metric_compatibility G z
      (((hG z hz).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp))
      (hsymNear z hz) (hpos z hz) y v w
  have htor (z : ℝ × EuclideanSpace ℝ (Fin 2)) (hz : z ∈ O)
      (v w : EuclideanSpace ℝ (Fin 2)) : Γ z v w = Γ z w v :=
    Frame.chartConnection_symm G z
      (((hG z hz).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp))
      (hsymNear z hz) v w
  have hid := surfaceActionDensity_second_boundary hΩ hO G P Γ q hG hP hΓ hq hmap
    hsym hcompat htor hsΩ
  dsimp only at hid
  rw [surfaceIndex_variationChart V D hs hx (htime s hs),
    surfaceEuler_variationChart hpotential V D hs hx (htime s hs),
    heuler s hs, sub_zero] at hid
  have hnearU : ∀ᶠ u in 𝓝 (0 : ℝ), (s, u) ∈ Ω :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hΩ.mem_nhds hsΩ)
  have hLnear : (fun u ↦ variationActionDensity V (s, u)) =ᶠ[𝓝 (0 : ℝ)]
      (fun u ↦ surfaceActionDensity G P q (s, u)) := by
    filter_upwards [hnearU] with u hu
    exact (surfaceActionDensity_variationChart V hu.1).symm
  have hL := variationActionDensity_contDiffOn hpotential V
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
    exact surfaceAccelerationBoundaryPair_variationChart V D (Ioo_subset_Icc_self hr.2)
      hr.1.2 (htime r hr.2)
  rw [hBnear.deriv_eq, ← derivWithin_of_mem_nhds hsN] at hid
  exact hraw'.trans hid

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
