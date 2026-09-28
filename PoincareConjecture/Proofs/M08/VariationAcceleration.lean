import PoincareConjecture.Proofs.M08.SecondVariationCoordinates
import PoincareConjecture.Proofs.M08.SecondVariationGeometry
import PoincareConjecture.Proofs.M08.JacobiClosedCoordinates
import PoincareConjecture.Proofs.M08.JacobiRepresentative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem pullbackCovariantDerivative_chart_formula_local {J C U : Set ℝ}
    (F : RicciFlow n M J) (time : ℝ → ℝ) (hU : IsOpen U)
    (x : M) (α : ℝ → M) (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : ContDiffOn ℝ ∞ c U)
    (hsrc : MapsTo α (C ∩ U) (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (Y : ∀ s, TangentSpace (𝓡 n) (α s))
    (hY : ∀ s ∈ C ∩ U, chartFrame x (c s) (α s) = Y s)
    (E : ParametricAlongCurveExtensionOn C α Y) {s : ℝ} (hs : s ∈ C) (hsU : s ∈ U)
    (hC : UniqueDiffWithinAt ℝ C s)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    pullbackCovariantDerivative F time α Y C E s =
      chartFrame x (deriv c s) (α s) +
        (F.connection (time s)).connection (chartFrame x (c s)) (α s)
          (chartFrame x (deriv ((extChartAt (𝓡 n) x) ∘ α) s) (α s)) := by
  have hD := hC.inter (hU.mem_nhds hsU)
  rw [pullbackCovariantDerivative_restrict F time inter_subset_left E hC hD hα]
  exact pullbackCovariantDerivative_chart_formula F time hU inter_subset_right x α c hc
    hsrc Y hY (restrictParametricSectionExtension inter_subset_left E) ⟨hs, hsU⟩ hD hα

def variationChartDomain {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (x : M) : Set (ℝ × ℝ) :=
  V.squareDomain ∩ (fun z : ℝ × ℝ ↦ V.squareFamily z.1 z.2) ⁻¹'
    (chartAt (EuclideanSpace ℝ (Fin n)) x).source

def variationChart {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (x : M) (z : ℝ × ℝ) : EuclideanSpace ℝ (Fin n) :=
  extChartAt (𝓡 n) x (V.squareFamily z.1 z.2)

theorem variationChartDomain_open {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (x : M) : IsOpen (variationChartDomain V x) :=
  V.square_smooth.continuousOn.isOpen_inter_preimage V.square_open
    (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source

theorem variationChart_contDiffOn {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (x : M) :
    ContDiffOn ℝ ∞ (variationChart V x) (variationChartDomain V x) := by
  have h := (contMDiffOn_extChartAt (I := 𝓡 n) (x := x)).comp
    (V.square_smooth.mono inter_subset_left) (fun z hz ↦ by
      simpa only [extChartAt_source] using hz.2)
  apply ContMDiffOn.contDiffOn
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact h

set_option maxHeartbeats 1800000 in
theorem variationEndpointAcceleration_chart {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V)
    {x : M} {s : ℝ} (hs : s ∈ sqrtParameterInterval τ₁ τ₂)
    (hx : V.baseSquareCurve s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    variationEndpointAcceleration V D s hs =
      chartFrame x
        (coordinatePartialU (coordinatePartialU (variationChart V x)) (s, 0) +
          closedChartChristoffel F T x (sqrtParameterInterval τ₁ τ₂)
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
  have htime (r : ℝ) (hr : r ∈ C) : T - r ^ 2 ∈ J := by
    apply p.time_mem
    have hr0 : 0 ≤ r := (Real.sqrt_nonneg τ₁).trans hr.1
    constructor
    · nlinarith [Real.sq_sqrt p.nonnegative, Real.sqrt_nonneg τ₁, hr.1]
    · nlinarith [Real.sq_sqrt (p.nonnegative.trans p.ordered.le), Real.sqrt_nonneg τ₂, hr.2]
  change variationEndpointAcceleration V D s hs = _ at hpb
  rw [hpb, hdc, hdq]
  change chartFrame x (coordinatePartialU (coordinatePartialU q) (s, 0))
      (V.baseSquareCurve s) +
    (F.connection (T - s ^ 2)).connection
      (chartFrame x (coordinatePartialU q (s, 0))) (V.baseSquareCurve s)
      (chartFrame x (coordinatePartialU q (s, 0)) (V.baseSquareCurve s)) = _
  rw [closedChartChristoffel_connection F T htime hx hs]
  exact ((trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace (𝓡 n)) x).symmL ℝ (V.baseSquareCurve s)).map_add _ _ |>.symm

end PoincareConjecture.M08
