import PoincareConjecture.Proofs.M08.VariationAcceleration
import PoincareConjecture.Proofs.M08.ClosedSectionExtension
import PoincareConjecture.Proofs.M08.ChartEulerEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

def parametricExtension_chartCoordinates {C : Set ℝ} {α : ℝ → M}
    {Y : ∀ s, TangentSpace (𝓡 n) (α s)}
    (E : ParametricAlongCurveExtensionOn C α Y) (x : M) (r : ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).continuousLinearMapAt
    ℝ (α r) (E.extension r (α r))

theorem exists_parametricExtension_chartCoordinates {C U : Set ℝ}
    (hU : IsOpen U) (hCU : C ⊆ U)
    (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (Y : ∀ s, TangentSpace (𝓡 n) (α s))
    (E : ParametricAlongCurveExtensionOn C α Y) {s : ℝ} (hs : s ∈ C)
    {x : M} (hx : α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source) :
    ∃ N : Set ℝ, IsOpen N ∧ s ∈ N ∧ N ⊆ U ∧
      MapsTo α N (chartAt (EuclideanSpace ℝ (Fin n)) x).source ∧
      ContDiffOn ℝ ∞ (parametricExtension_chartCoordinates E x) N ∧
      ∀ r ∈ C ∩ N, chartFrame x (parametricExtension_chartCoordinates E x r) (α r) = Y r := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x
  let U₁ := U ∩ (fun r : ℝ ↦ (r, α r)) ⁻¹' E.domain
  let N := U₁ ∩ α ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) x).source
  have hU₁ : IsOpen U₁ := (continuousOn_id.prodMk hα.continuousOn).isOpen_inter_preimage
    hU E.open_domain
  have hN : IsOpen N := (hα.continuousOn.mono inter_subset_left).isOpen_inter_preimage
    hU₁ (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source
  refine ⟨N, hN, ⟨⟨hCU hs, E.graph_mem s hs⟩, hx⟩,
    inter_subset_left.trans inter_subset_left, fun _ hr ↦ hr.2, ?_, ?_⟩
  · intro r hr
    have hcoord := (parametricExtension_chart_contMDiffAt E hr.2 hr.1.2).comp r
      (contMDiffAt_id.prodMk ((hα r hr.1.1).contMDiffAt (hU.mem_nhds hr.1.1)))
    exact hcoord.contDiffAt.contDiffWithinAt
  · intro r hr
    exact (e.symmL_continuousLinearMapAt hr.2.2 _).trans (E.agrees r hr.1)

theorem pullbackCovariantDerivative_chart_extension {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) {a b : ℝ} (hab : a < b)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J)
    {N : Set ℝ} (hN : IsOpen N) (x : M)
    (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α N)
    (Y : ∀ s, TangentSpace (𝓡 n) (α s))
    (E : ParametricAlongCurveExtensionOn (Icc a b) α Y)
    (hsrc : MapsTo α N (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hc : ContDiffOn ℝ ∞ (parametricExtension_chartCoordinates E x) N)
    (hrep : ∀ r ∈ Icc a b ∩ N,
      chartFrame x (parametricExtension_chartCoordinates E x r) (α r) = Y r)
    {s : ℝ} (hs : s ∈ Icc a b ∩ N) :
    pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α Y (Icc a b) E s =
      chartFrame x (deriv (parametricExtension_chartCoordinates E x) s +
        closedChartChristoffel F T x (Icc a b) (s, extChartAt (𝓡 n) x (α s))
          (deriv ((extChartAt (𝓡 n) x) ∘ α) s)
          (parametricExtension_chartCoordinates E x s)) (α s) := by
  have hαs := ((hα s hs.2).contMDiffAt (hN.mem_nhds hs.2)).mdifferentiableAt (by simp)
  rw [pullbackCovariantDerivative_chart_formula_local F (fun t ↦ T - t ^ 2)
    hN x α (parametricExtension_chartCoordinates E x) hc (fun t ht ↦ hsrc ht.2)
    Y hrep E hs.1 hs.2 (uniqueDiffOn_Icc hab s hs.1) hαs,
    closedChartChristoffel_connection F T htime (hsrc hs.2) hs.1]
  exact ((trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)) x).symmL
    ℝ (α s)).map_add _ _ |>.symm

set_option maxHeartbeats 1200000 in
theorem pullbackCovariantDerivative_chart_contMDiffOn {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) {a b : ℝ} (hab : a < b)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J)
    {N : Set ℝ} (hN : IsOpen N) (x : M)
    (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α N)
    (Y : ∀ s, TangentSpace (𝓡 n) (α s))
    (E : ParametricAlongCurveExtensionOn (Icc a b) α Y)
    (hsrc : MapsTo α N (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hc : ContDiffOn ℝ ∞ (parametricExtension_chartCoordinates E x) N)
    (hrep : ∀ r ∈ Icc a b ∩ N,
      chartFrame x (parametricExtension_chartCoordinates E x r) (α r) = Y r) :
    ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s)
        (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α Y (Icc a b) E s))
      (Icc a b ∩ N) := by
  let C := Icc a b
  have hC : UniqueDiffOn ℝ C := uniqueDiffOn_Icc hab
  let c := parametricExtension_chartCoordinates E x
  let q := (extChartAt (𝓡 n) x) ∘ α
  let v := deriv q
  let d := fun r : ℝ ↦ deriv c r + closedChartChristoffel F T x C
    (r, extChartAt (𝓡 n) x (α r)) (v r) (c r)
  have hq : ContDiffOn ℝ ∞ q N := chart_curve_contDiffOn x α hα hsrc
  have hv : ContDiffOn ℝ ∞ v N := hq.deriv_of_isOpen hN (by simp)
  have hdc : ContDiffOn ℝ ∞ (deriv c) N := hc.deriv_of_isOpen hN (by simp)
  have hpoint : ContDiffOn ℝ ∞ (fun r : ℝ ↦
      ((r, extChartAt (𝓡 n) x (α r)), (v r, c r))) (C ∩ N) :=
    (contDiffOn_id.prodMk (hq.mono inter_subset_right)).prodMk
      ((hv.mono inter_subset_right).prodMk (hc.mono inter_subset_right))
  have hmap : MapsTo (fun r : ℝ ↦
      ((r, extChartAt (𝓡 n) x (α r)), (v r, c r))) (C ∩ N)
      ((C ×ˢ (extChartAt (𝓡 n) x).target) ×ˢ univ) := by
    intro r hr
    refine ⟨⟨hr.1, ?_⟩, mem_univ _⟩
    exact (extChartAt (𝓡 n) x).map_source
      (by simpa only [extChartAt_source] using hsrc hr.2)
  have hΓ : ContDiffOn ℝ ∞ (fun r : ℝ ↦ closedChartChristoffel F T x C
      (r, extChartAt (𝓡 n) x (α r)) (v r) (c r)) (C ∩ N) :=
    (closedChartChristoffel_contDiffOn F T x hC htime).comp
      (f := fun r : ℝ ↦ ((r, extChartAt (𝓡 n) x (α r)), (v r, c r))) hpoint hmap
  have hd : ContDiffOn ℝ ∞ d (C ∩ N) := (hdc.mono inter_subset_right).add hΓ
  have hαN : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α (C ∩ N) :=
    hα.mono inter_subset_right
  have hfield : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun r ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α r)
        (chartFrame x (d r) (α r))) (C ∩ N) :=
    closedChartField_contMDiffOn x α d hαN hd (fun r hr ↦ hsrc hr.2)
  apply hfield.congr
  intro r hr
  apply congrArg (fun w : TangentSpace (𝓡 n) (α r) ↦
    Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α r) w)
  exact pullbackCovariantDerivative_chart_extension F T hab htime hN x α hα Y E
    hsrc hc hrep hr

theorem pullbackCovariantDerivative_contMDiffOn {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) {a b : ℝ} (hab : a < b)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J)
    {U : Set ℝ} (hU : IsOpen U) (hCU : Icc a b ⊆ U)
    (α : ℝ → M) (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (Y : ∀ s, TangentSpace (𝓡 n) (α s))
    (E : ParametricAlongCurveExtensionOn (Icc a b) α Y) :
    ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓡 n)) ∞
      (fun s ↦ Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (α s)
        (pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) α Y (Icc a b) E s))
      (Icc a b) := by
  intro s hs
  let x := α s
  obtain ⟨N, hN, hsN, hNU, hsrc, hc, hrep⟩ :=
    exists_parametricExtension_chartCoordinates hU hCU α hα Y E hs
      (show α s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source from mem_chart_source _ _)
  have hactual := pullbackCovariantDerivative_chart_contMDiffOn F T hab htime hN x α
    (hα.mono hNU) Y E hsrc hc hrep
  exact (contMDiffWithinAt_inter (hN.mem_nhds hsN)).mp (hactual s ⟨hs, hsN⟩)

theorem squareVariationField_agrees_backward {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) {s : ℝ} (hs : s ∈ sqrtParameterInterval τ₁ τ₂) :
    squareVariationField V s = variationField V (s ^ 2) := by
  have hnear : V.squareFamily s =ᶠ[𝓝 (0 : ℝ)] V.family (s ^ 2) :=
    Filter.eventually_of_mem
      (isOpen_Ioo.mem_nhds ⟨neg_neg_of_pos V.radius_pos, V.radius_pos⟩)
      (fun v hv ↦ V.square_agrees s hs v hv)
  simp only [squareVariationField, variationField, tangent_cast_eq, curveVelocity,
    hnear.mfderiv_eq]
  rfl

def variationSqrtRegularField {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V) :
    SqrtRegularField (variationSqrtRegularPath V) (variationField V) := by
  let R := variationSqrtRegularPath V
  let DY := pullbackCovariantDerivative F (fun r ↦ T - r ^ 2) V.baseSquareCurve
    (squareVariationField V) (sqrtParameterInterval τ₁ τ₂) D.variation_extension
  have hDY := pullbackCovariantDerivative_contMDiffOn F T
    (Real.sqrt_lt_sqrt p.nonnegative p.ordered)
    (fun s hs ↦ p.time_mem (s ^ 2) (square_mem_backward_interval p hs))
    R.open_domain R.interval_subset R.curve R.smooth (squareVariationField V) D.variation_extension
  let E := Classical.choice (exists_closedSectionExtension
    (Real.sqrt_lt_sqrt p.nonnegative p.ordered)
    R.open_domain R.interval_subset R.curve R.smooth DY hDY)
  refine {
    field := squareVariationField V
    agrees := ?_
    extension := D.variation_extension
    derivative_extension := E }
  intro s hs
  rw [tangent_cast_eq]
  exact squareVariationField_agrees_backward V hs

def variationRegularizedGeodesicData {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (V : LVariation F T τ₁ τ₂ p) (D : LVariationDerivativeData V)
    (R : RegularizedLGeodesicData p) : RegularizedLGeodesicData p where
  path := variationSqrtRegularPath V
  velocity_extension := D.velocity_extension
  equation s hs W := variation_regularizedEulerResidual_zero V D R hs W

end PoincareConjecture.M08
