import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Acceleration
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Frame.CoefficientRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.Action

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variation.Geometry

open ReducedLengthMinimum.Variational

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def variationAccelerationField {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V) (s : ℝ) :
    TangentSpace (𝓡 n) (V.baseSquareCurve s) := by
  classical
  exact if hs : s ∈ sqrtParameterInterval τ₁ τ₂ then
    variationEndpointAcceleration V D s hs else 0

theorem variationAccelerationField_eq {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V)
    {s : ℝ} (hs : s ∈ sqrtParameterInterval τ₁ τ₂) :
    variationAccelerationField V D s = variationEndpointAcceleration V D s hs := by
  simp only [variationAccelerationField, dif_pos hs]

set_option maxHeartbeats 2000000 in
theorem variationAccelerationField_contMDiffOn {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V)
    (hclock : ∀ s ∈ sqrtParameterInterval τ₁ τ₂,
      s ∈ interior ((fun r : ℝ => T - r ^ 2) ⁻¹' J)) :
    ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (V.baseSquareCurve s) (variationAccelerationField V D s))
      (sqrtParameterInterval τ₁ τ₂) := by
  let C := sqrtParameterInterval τ₁ τ₂
  have hC : UniqueDiffOn ℝ C := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.nonnegative p.ordered)
  have hzero : (0 : ℝ) ∈ V.parameterDomain := ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  have htime (r : ℝ) (hr : r ∈ C) : T - r ^ 2 ∈ J := by
    apply p.time_mem
    have hr0 : 0 ≤ r := (Real.sqrt_nonneg τ₁).trans hr.1
    constructor
    · nlinarith [Real.sq_sqrt p.nonnegative, Real.sqrt_nonneg τ₁, hr.1]
    · nlinarith [Real.sq_sqrt (p.nonnegative.trans p.ordered.le), Real.sqrt_nonneg τ₂, hr.2]
  intro s hs
  let x := V.baseSquareCurve s
  let Ω := variationChartDomain V x
  let N := (fun r : ℝ ↦ (r, (0 : ℝ))) ⁻¹' Ω
  let q := variationChart V x
  let y := fun r : ℝ ↦ coordinatePartialU q (r, 0)
  let z := fun r : ℝ ↦ coordinatePartialU (coordinatePartialU q) (r, 0) +
    Frame.chartConnection (chartActionMetric F T x) (r, q (r, 0)) (y r) (y r)
  have hΩ : IsOpen Ω := variationChartDomain_open V x
  have hN : IsOpen N := hΩ.preimage (continuous_id.prodMk continuous_const)
  have hsN : s ∈ N := ⟨V.square_contains ⟨hs, hzero⟩, mem_chart_source _ _⟩
  have hq : ContDiffOn ℝ ∞ q Ω := variationChart_contDiffOn V x
  have hqU := coordinatePartialU_contDiffOn hΩ q hq
  have hqUU := coordinatePartialU_contDiffOn hΩ _ hqU
  have hslice : MapsTo (fun r : ℝ ↦ (r, (0 : ℝ))) N Ω := fun r hr ↦ hr
  have hqN : ContDiffOn ℝ ∞ (fun r : ℝ ↦ q (r, 0)) N :=
    hq.comp (contDiffOn_id.prodMk contDiffOn_const) hslice
  have hy : ContDiffOn ℝ ∞ y N :=
    hqU.comp (contDiffOn_id.prodMk contDiffOn_const) hslice
  have hz₀ : ContDiffOn ℝ ∞ (fun r : ℝ ↦ coordinatePartialU (coordinatePartialU q) (r, 0)) N :=
    hqUU.comp (contDiffOn_id.prodMk contDiffOn_const) hslice
  have hsrc : MapsTo V.baseSquareCurve (C ∩ N)
      (chartAt (EuclideanSpace ℝ (Fin n)) x).source := fun r hr ↦ hr.2.2
  have hmap : MapsTo (fun r : ℝ ↦ ((r, q (r, 0)), (y r, y r))) (C ∩ N)
      {q : (ℝ × EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
        q.1 ∈ chartActionDomain F T x} := by
    intro r hr
    refine ⟨hclock r hr.1, ?_⟩
    exact (extChartAt (𝓡 n) x).map_source (by
      simpa only [extChartAt_source, LVariation.baseSquareCurve] using hsrc hr)
  have hk : ContDiffOn ℝ ∞
      (fun r : ℝ ↦ ((r, q (r, 0)), (y r, y r))) (C ∩ N) :=
    (contDiffOn_id.prodMk (hqN.mono inter_subset_right)).prodMk
      ((hy.mono inter_subset_right).prodMk (hy.mono inter_subset_right))
  have hΓ := (Frame.chartConnection_smooth (chartActionMetric F T x)
    (chartActionDomain F T x) (chartActionDomain_open F T x)
    (chartActionMetric_contDiffOn F T x) (fun z hz => chartActionMetric_pos F T x hz)).comp hk hmap
  have hz : ContDiffOn ℝ ∞ z (C ∩ N) := (hz₀.mono inter_subset_right).add hΓ
  have hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ V.baseSquareCurve (C ∩ N) :=
    V.square_smooth.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
      (fun r hr ↦ hr.2.1)
  have hfield := chartFrame_curve_contMDiffOn x V.baseSquareCurve z (C ∩ N) hα hz (fun r hr => hsrc hr)
  have hactual : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun r ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (V.baseSquareCurve r) (variationAccelerationField V D r)) (C ∩ N) := by
    apply hfield.congr
    intro r hr
    congr 1
    rw [variationAccelerationField_eq V D hr.1]
    exact variationEndpointAcceleration_chart V D hr.1 (hsrc hr) (hclock r hr.1)
  exact (contMDiffWithinAt_inter (hN.mem_nhds hsN)).mp (hactual s ⟨hs, hsN⟩)

def variationAccelerationBoundaryPair {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V) (s : ℝ) : ℝ :=
  (F.metric (T - s ^ 2)).inner (V.baseSquareCurve s)
    (curveVelocityWithin (n := n) V.baseSquareCurve (sqrtParameterInterval τ₁ τ₂) s)
    (variationAccelerationField V D s)

set_option maxHeartbeats 1000000 in
theorem variationAccelerationBoundaryPair_contDiffOn {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V)
    (hclock : ∀ s ∈ sqrtParameterInterval τ₁ τ₂,
      s ∈ interior ((fun r : ℝ => T - r ^ 2) ⁻¹' J)) :
    ContDiffOn ℝ ∞ (variationAccelerationBoundaryPair V D) (sqrtParameterInterval τ₁ τ₂) := by
  let C := sqrtParameterInterval τ₁ τ₂
  let U := (fun s : ℝ ↦ (s, (0 : ℝ))) ⁻¹' V.squareDomain
  have hU : IsOpen U := V.square_open.preimage (continuous_id.prodMk continuous_const)
  have hCU : C ⊆ U := fun s hs ↦
    V.square_contains ⟨hs, neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  have hC : UniqueDiffOn ℝ C := uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.nonnegative p.ordered)
  have hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ V.baseSquareCurve U :=
    V.square_smooth.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun s hs ↦ hs)
  have hA : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (V.baseSquareCurve s)
        (curveVelocityWithin (n := n) V.baseSquareCurve C s)) C := by
    apply ((contMDiffOn_mfderiv_const_apply hU V.baseSquareCurve hα (1 : ℝ)).mono hCU).congr
    intro s hs
    apply congrArg (fun w : TangentSpace (𝓡 n) (V.baseSquareCurve s) ↦
      Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (V.baseSquareCurve s) w)
    unfold curveVelocityWithin
    rw [mfderivWithin_eq_mfderiv (hC.uniqueMDiffOn s hs)
      (((hα s (hCU hs)).contMDiffAt (hU.mem_nhds (hCU hs))).mdifferentiableAt (by simp))]
  have ht : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun s : ℝ ↦ T - s ^ 2) C :=
    (contDiff_const.sub (contDiff_id.pow 2)).contMDiff.contMDiffOn
  have hmem : MapsTo (fun s : ℝ ↦ T - s ^ 2) C J := by
    intro s hs
    apply p.time_mem
    have hs0 : 0 ≤ s := (Real.sqrt_nonneg τ₁).trans hs.1
    constructor
    · nlinarith [Real.sq_sqrt p.nonnegative, Real.sqrt_nonneg τ₁, hs.1]
    · nlinarith [Real.sq_sqrt (p.nonnegative.trans p.ordered.le), Real.sqrt_nonneg τ₂, hs.2]
  exact (movingMetric_pair_contMDiffOn F (fun s : ℝ ↦ T - s ^ 2) V.baseSquareCurve
    (curveVelocityWithin (n := n) V.baseSquareCurve C) (variationAccelerationField V D)
    ht (hα.mono hCU) hA (variationAccelerationField_contMDiffOn V D hclock) hmem).contDiffOn

theorem secondVariationBoundaryTerm_eq_accelerationPair {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V) :
    secondVariationBoundaryTerm V D =
      variationAccelerationBoundaryPair V D (Real.sqrt τ₂) -
        variationAccelerationBoundaryPair V D (Real.sqrt τ₁) := by
  have hleft : Real.sqrt τ₁ ∈ sqrtParameterInterval τ₁ τ₂ :=
    ⟨le_rfl, Real.sqrt_le_sqrt p.ordered.le⟩
  have hright : Real.sqrt τ₂ ∈ sqrtParameterInterval τ₁ τ₂ :=
    ⟨Real.sqrt_le_sqrt p.ordered.le, le_rfl⟩
  simp only [secondVariationBoundaryTerm, variationAccelerationBoundaryPair,
    variationAccelerationField_eq V D hleft, variationAccelerationField_eq V D hright]

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
