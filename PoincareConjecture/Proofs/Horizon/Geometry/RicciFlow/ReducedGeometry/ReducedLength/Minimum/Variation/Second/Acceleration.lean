import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Second.Fields









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

set_option maxHeartbeats 1800000 in
theorem variationEndpointAcceleration_chart {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V)
    {x : M} {s : ℝ} (hs : s ∈ sqrtParameterInterval τ₁ τ₂)
    (hx : V.baseSquareCurve s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (ht : s ∈ interior ((fun r : ℝ => T - r ^ 2) ⁻¹' J)) :
    variationEndpointAcceleration V D s hs =
      chartFrame x
        (coordinatePartialU (coordinatePartialU (variationChart V x)) (s, 0) +
          Frame.chartConnection (chartActionMetric F T x)
            (s, variationChart V x (s, 0))
            (coordinatePartialU (variationChart V x) (s, 0))
            (coordinatePartialU (variationChart V x) (s, 0))) (V.baseSquareCurve s) := by
  let C := sqrtParameterInterval τ₁ τ₂
  let Ω := variationChartDomain V x
  let q := variationChart V x
  let α := V.squareFamily s
  let U := (fun u : ℝ ↦ (s, u)) ⁻¹' Ω
  let c := fun u : ℝ ↦ coordinatePartialU q (s, u)
  have hΩ : IsOpen Ω := variationChartDomain_open V x
  have hq : ContDiffOn ℝ ∞ q Ω := variationChart_contDiffOn V x
  have hU : IsOpen U := hΩ.preimage (continuous_const.prodMk continuous_id)
  have hzero : (0 : ℝ) ∈ V.parameterDomain := ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩
  have hzeroU : (0 : ℝ) ∈ U := ⟨V.square_contains ⟨hs, hzero⟩, hx⟩
  have hc : ContDiffOn ℝ ∞ c U :=
    (coordinatePartialU_contDiffOn hΩ q hq).comp
      (contDiffOn_const.prodMk contDiffOn_id) (fun u hu ↦ hu)
  have hα (u : ℝ) (hu : u ∈ U) : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α u :=
    (((V.square_smooth (s, u) hu.1).contMDiffAt
      (V.square_open.mem_nhds hu.1)).mdifferentiableAt (by simp)).comp u
        (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  have hsrc : MapsTo α (V.parameterDomain ∩ U)
      (chartAt (EuclideanSpace ℝ (Fin n)) x).source := fun u hu ↦ hu.2.2
  have hfield (u : ℝ) (hu : u ∈ V.parameterDomain ∩ U) :
      chartFrame x (c u) (α u) = curveVelocityWithin (n := n) α V.parameterDomain u := by
    have hd := (coordinateSlice_snd_hasDerivAt q
      (((hq (s, u) hu.2).contDiffAt (hΩ.mem_nhds hu.2)).differentiableAt (by simp))).deriv
    change deriv ((extChartAt (𝓡 n) x) ∘ α) u = c u at hd
    rw [← hd, chartFrame_curveVelocity (hsrc hu) (hα u hu.2)]
    unfold curveVelocityWithin curveVelocity
    change (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) α u) 1 =
      (mfderivWithin (𝓘(ℝ, ℝ)) (𝓡 n) α (Ioo (-V.radius) V.radius) u) 1
    rw [mfderivWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hu.1)]
  have hpb := pullbackCovariantDerivative_chart_formula_local F (fun _ ↦ T - s ^ 2)
    hU x α c hc hsrc _ hfield (D.endpoint_extension s hs) hzero hzeroU
      (isOpen_Ioo.uniqueDiffWithinAt hzero) (hα 0 hzeroU)
  have hdc := (coordinateSlice_snd_hasDerivAt (coordinatePartialU q)
    ((((coordinatePartialU_contDiffOn hΩ q hq) (s, 0) hzeroU).contDiffAt
      (hΩ.mem_nhds hzeroU)).differentiableAt (by simp))).deriv
  have hdq := (coordinateSlice_snd_hasDerivAt q
    (((hq (s, 0) hzeroU).contDiffAt (hΩ.mem_nhds hzeroU)).differentiableAt (by simp))).deriv
  change deriv c 0 = coordinatePartialU (coordinatePartialU q) (s, 0) at hdc
  change deriv ((extChartAt (𝓡 n) x) ∘ α) 0 = coordinatePartialU q (s, 0) at hdq
  change variationEndpointAcceleration V D s hs = _ at hpb
  rw [hpb, hdc, hdq]
  change chartFrame x (coordinatePartialU (coordinatePartialU q) (s, 0))
      (V.baseSquareCurve s) +
    (F.connection (T - s ^ 2)).connection
      (chartFrame x (coordinatePartialU q (s, 0))) (V.baseSquareCurve s)
      (chartFrame x (coordinatePartialU q (s, 0)) (V.baseSquareCurve s)) = _
  rw [Frame.chartConnection_eq_retainedConnection_squareDomain F T s x _ hx ht]
  exact ((trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n)) x).symmL ℝ (V.baseSquareCurve s)).map_add _ _ |>.symm


end PoincareConjecture.ReducedLengthMinimum.Variation.Geometry
