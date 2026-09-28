import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.Action
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.MetricPair








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

omit [IsManifold (𝓡 n) ∞ M] in
theorem curveVelocityWithin_eq_of_open_subset {I C : Set ℝ} (hI : IsOpen I)
    (hIC : I ⊆ C) (α : ℝ → M) {s : ℝ} (hs : s ∈ I) :
    curveVelocityWithin (n := n) α I s = curveVelocityWithin (n := n) α C s := by
  unfold curveVelocityWithin
  rw [mfderivWithin_of_mem_nhds (hI.mem_nhds hs),
    mfderivWithin_of_mem_nhds (mem_of_superset (hI.mem_nhds hs) hIC)]

def restrictInteriorVelocityExtension {I C : Set ℝ} (hI : IsOpen I)
    (hIC : I ⊆ C) (α : ℝ → M)
    (E : ParametricAlongCurveExtensionOn C α (curveVelocityWithin (n := n) α C)) :
    ParametricAlongCurveExtensionOn I α (curveVelocityWithin (n := n) α I) where
  extension := E.extension
  domain := E.domain
  open_domain := E.open_domain
  graph_mem s hs := E.graph_mem s (hIC hs)
  smooth := E.smooth
  agrees s hs := (E.agrees s (hIC hs)).trans
    (curveVelocityWithin_eq_of_open_subset hI hIC α hs).symm

theorem chartActionPotential_apply {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    {x y : M} (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) (s : ℝ) :
    chartActionPotential F T x (s, extChartAt (𝓡 n) x y) =
      2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature y := by
  have hy' : y ∈ (extChartAt (𝓡 n) x).source := by simpa only [extChartAt_source] using hy
  simp only [chartActionPotential, (extChartAt (𝓡 n) x).left_inv hy']

theorem regularizedLIntegrand_eq_chart {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    {α : ℝ → M} {x : M} {s : ℝ}
    (hx : α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    regularizedLIntegrand F T α s =
      chartActionMetric F T x (s, extChartAt (𝓡 n) x (α s))
        (deriv ((extChartAt (𝓡 n) x) ∘ α) s)
        (deriv ((extChartAt (𝓡 n) x) ∘ α) s) / 2 +
      chartActionPotential F T x (s, extChartAt (𝓡 n) x (α s)) := by
  rw [chartActionMetric_apply F T hx, chartActionPotential_apply F T hx,
    chartFrame_curveVelocity hx hα]
  unfold regularizedLIntegrand
  ring

set_option maxHeartbeats 2000000 in
theorem firstVariation_density_identity {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax τ₁ τ₂ : ℝ} (hpotential : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun z : ℝ × M => 2 * z.1 ^ 2 *
        (F.connection (T - z.1 ^ 2)).scalarCurvature z.2))
    (hwindow : Icc (T - τmax) T ⊆ J) (hτ₂ : τ₂ ≤ τmax)
    {p : BackwardTimePath F T τ₁ τ₂} (V : LVariation F T τ₁ τ₂ p)
    (D : LVariationDerivativeData V) {s : ℝ}
    (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    variationParameterDeriv (sqrtParameterInterval τ₁ τ₂) V.parameterDomain
        (variationActionDensity V) (s, 0) =
      derivWithin (variationBoundaryPair V) (sqrtParameterInterval τ₁ τ₂) s -
        regularizedEulerResidual F T V.baseSquareCurve (sqrtParameterInterval τ₁ τ₂)
          D.velocity_extension s (squareVariationField V s) := by
  let C := sqrtParameterInterval τ₁ τ₂
  let I := Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)
  let α := V.baseSquareCurve
  let H := fun z : ℝ × ℝ ↦ V.squareFamily z.1 z.2
  let x := α s
  let e := extChartAt (𝓡 n) x
  let z := fun a : ℝ × ℝ ↦ e (H a)
  let Ω := V.squareDomain ∩ H ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) x).source
  let q := fun r ↦ deriv (fun t ↦ z (t, 0)) r
  let w := fun r ↦ deriv (fun u ↦ z (r, u)) 0
  let qv := fun u ↦ deriv (fun r ↦ z (r, u)) s
  have hzero : (0 : ℝ) ∈ V.parameterDomain := ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  have hsC : s ∈ C := Ioo_subset_Icc_self hs
  have hΩ : IsOpen Ω := V.square_smooth.continuousOn.isOpen_inter_preimage
    V.square_open (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source
  have hsΩ : (s, (0 : ℝ)) ∈ Ω :=
    ⟨V.square_contains ⟨hsC, hzero⟩, mem_chart_source _ _⟩
  have hH (a : ℝ × ℝ) (ha : a ∈ Ω) :
      MDifferentiableAt ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, ℝ))) (𝓡 n) H a :=
    ((V.square_smooth a ha.1).contMDiffAt (V.square_open.mem_nhds ha.1)).mdifferentiableAt
      (by simp)
  have hz : ContDiffOn ℝ ∞ z Ω := by
    have h := (contMDiffOn_extChartAt (I := 𝓡 n) (x := x)).comp
      (V.square_smooth.mono inter_subset_left) (fun a ha ↦ by
        simpa only [extChartAt_source] using ha.2)
    apply ContMDiffOn.contDiffOn
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact h
  obtain ⟨k, hqv, hw⟩ := coordinate_mixed_hasDerivAt hΩ z hz hsΩ
  have hzd : DifferentiableAt ℝ z (s, 0) :=
    ((hz (s, 0) hsΩ).contDiffAt (hΩ.mem_nhds hsΩ)).differentiableAt (by simp)
  have hzv : HasDerivAt (fun u ↦ z (s, u)) (w s) 0 :=
    ((coordinateSlice_snd_hasDerivAt z hzd).differentiableAt).hasDerivAt
  have hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s :=
    (hH (s, 0) hsΩ).comp s (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
  have hx : α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := mem_chart_source _ _
  have ht := backwardSquareTime_mem_interior hwindow p.nonnegative p.ordered hτ₂ hs
  have hdom : (s, e (α s)) ∈ chartActionDomain F T x := by
    refine ⟨squareTime_mem_interior_preimage ht, e.map_source ?_⟩
    simpa only [e, extChartAt_source] using hx
  have hG := hasFDerivAt_spatial (chartActionDomain_open F T x) _
    (chartActionMetric_contDiffOn F T x) hdom
  have hV := hasFDerivAt_spatial (chartActionDomain_open F T x) _
    (chartActionPotential_contDiffOn F T hpotential x) hdom
  have hsym (v v' : EuclideanSpace ℝ (Fin n)) :
    chartActionMetric F T x (s, z (s, 0)) v v' =
        chartActionMetric F T x (s, z (s, 0)) v' v := by
    change chartActionMetric F T x (s, extChartAt (𝓡 n) x (α s)) v v' =
      chartActionMetric F T x (s, extChartAt (𝓡 n) x (α s)) v' v
    rw [chartActionMetric_apply F T hx, chartActionMetric_apply F T hx]
    exact (F.metric (T - s ^ 2)).symm _ _ _
  have hraw := chart_density_hasDerivAt (fun y ↦ chartActionMetric F T x (s, y))
    (fun y ↦ chartActionPotential F T x (s, y)) _ _ hG hV hzv hqv hsym
  have hnearU : ∀ᶠ u in 𝓝 (0 : ℝ), (s, u) ∈ Ω :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hΩ.mem_nhds hsΩ)
  have hraw' := hraw.congr_of_eventuallyEq (show
      (fun u ↦ variationActionDensity V (s, u)) =ᶠ[𝓝 (0 : ℝ)] _ from by
    filter_upwards [hnearU] with u hu
    exact regularizedLIntegrand_eq_chart F T hu.2
      ((hH (s, u) hu).comp s (mdifferentiableAt_id.prodMk mdifferentiableAt_const)))
  have hrawActual := hasDerivAt_variationParameter isOpen_Ioo (variationActionDensity V)
    (variationActionDensity_contDiffOn hpotential V) hsC hzero
  have hrawEq := hrawActual.unique hraw'
  change variationParameterDeriv C V.parameterDomain (variationActionDensity V) (s, 0) = _
    at hrawEq
  let E := restrictInteriorVelocityExtension isOpen_Ioo Ioo_subset_Icc_self α D.velocity_extension
  have hB := parametricExtension_metric_pair_moving_graph F T isOpen_Ioo E hs hx hα ht hw
  have hwfield (r : ℝ) (hr : (r, (0 : ℝ)) ∈ Ω) :
      chartFrame x (w r) (α r) = squareVariationField V r :=
    chartFrame_curveVelocity hr.2
      ((hH (r, 0) hr).comp 0 (mdifferentiableAt_const.prodMk mdifferentiableAt_id))
  have hnearS : ∀ᶠ r in 𝓝 s, (r, (0 : ℝ)) ∈ Ω :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hΩ.mem_nhds hsΩ)
  have hB' := hB.congr_of_eventuallyEq (show variationBoundaryPair V =ᶠ[𝓝 s] _ from by
    filter_upwards [hnearS, isOpen_Ioo.mem_nhds hs] with r hr hrI
    rw [E.agrees r hrI, hwfield r hr,
      curveVelocityWithin_eq_of_open_subset isOpen_Ioo Ioo_subset_Icc_self α hrI]
    rfl)
  have hBDeriv := hB'.hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.nonnegative p.ordered) s hsC)
  have hR (W : TangentSpace (𝓡 n) (α s)) :
      regularizedEulerResidual F T α I E s W =
        regularizedEulerResidual F T α C D.velocity_extension s W := by
    unfold regularizedEulerResidual pullbackCovariantDerivative E restrictInteriorVelocityExtension
    rw [curveVelocityWithin_eq_of_open_subset isOpen_Ioo Ioo_subset_Icc_self α hs]
    rfl
  have hpot := chartActionPotential_spatial_apply F T hpotential hx ht (w s)
  change variationParameterDeriv C V.parameterDomain (variationActionDensity V) (s, 0) =
    derivWithin (variationBoundaryPair V) C s -
      regularizedEulerResidual F T α C D.velocity_extension s (squareVariationField V s)
  change derivWithin (variationBoundaryPair V) C s = _ at hBDeriv
  rw [hrawEq, hBDeriv, ← hR]
  unfold regularizedEulerResidual scalarCurvatureDifferential
  rw [← hwfield s hsΩ, ← hpot]
  dsimp only [q, w, qv, α, z, H, e, I, LVariation.baseSquareCurve, Function.comp_def]
  ring

end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
