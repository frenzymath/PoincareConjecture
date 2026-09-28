import PoincareConjecture.Proofs.M08.SupportedChartVariation
import PoincareConjecture.Proofs.M08.VariationChartFields

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τ₁ τ₂ : ℝ}
  {p : BackwardTimePath F T τ₁ τ₂}

set_option maxHeartbeats 1800000 in
theorem supportedChartVariation_squareField (V W : LVariation F T τ₁ τ₂ p)
    (x : M) (η : ℝ → EuclideanSpace ℝ (Fin n)) (hη : ContDiff ℝ ∞ η) (c : ℝ)
    (hfamily : ∀ s v, W.squareFamily s v = supportedChartFamily V x η c (s, v))
    (hsrc : ∀ s ∈ sqrtParameterInterval τ₁ τ₂, s ∈ tsupport η →
      V.baseSquareCurve s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    {s : ℝ} (hs : s ∈ sqrtParameterInterval τ₁ τ₂) :
    squareVariationField W s = squareVariationField V s +
      c • chartFrame x (η s) (V.baseSquareCurve s) := by
  by_cases hsupport : s ∈ tsupport η
  swap
  · have hcurve : W.squareFamily s = V.squareFamily s := by
      funext v
      exact (hfamily s v).trans
        (supportedChartFamily_eq_of_not_support V x η c (z := (s, v)) hsupport)
    have hηzero : η s = 0 := image_eq_zero_of_notMem_tsupport hsupport
    simp only [squareVariationField, hηzero, chartFrame, map_zero, smul_zero, add_zero]
    change curveVelocity (W.squareFamily s) 0 = curveVelocity (V.squareFamily s) 0
    rw [hcurve]
  have hx := hsrc s hs hsupport
  have hbase : W.baseSquareCurve s = V.baseSquareCurve s :=
    (hfamily s 0).trans (supportedChartFamily_at_zero V x η c hsrc hs)
  have hxW : W.baseSquareCurve s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) x).source := by
    rw [hbase]
    exact hx
  let U := variationChartDomain V x ∩
    supportedChartShift V x η c ⁻¹' (extChartAt (𝓡 n) x).target
  have hU : IsOpen U := (supportedChartShift_contDiffOn V x η hη c).continuousOn.isOpen_inter_preimage
    (variationChartDomain_open V x) (isOpen_extChartAt_target (I := 𝓡 n) x)
  have hsV : (s, (0 : ℝ)) ∈ variationChartDomain V x :=
    ⟨V.square_contains ⟨hs, neg_neg_of_pos V.radius_pos, V.radius_pos⟩, hx⟩
  have hsU : (s, (0 : ℝ)) ∈ U := by
    refine ⟨hsV, ?_⟩
    simp only [mem_preimage, supportedChartShift, zero_mul, zero_smul, add_zero, variationChart]
    exact (extChartAt (𝓡 n) x).map_source
      (by simpa only [extChartAt_source, LVariation.baseSquareCurve] using hx)
  have hnear : ∀ᶠ v in 𝓝 (0 : ℝ), (s, v) ∈ U :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hU.mem_nhds hsU)
  have heq : ((extChartAt (𝓡 n) x) ∘ W.squareFamily s) =ᶠ[𝓝 (0 : ℝ)]
      (fun v ↦ supportedChartShift V x η c (s, v)) := by
    filter_upwards [hnear] with v hv
    simp only [Function.comp_apply]
    rw [hfamily s v, supportedChartFamily_eq_chart V x η c (z := (s, v)) hv.1.2]
    exact (extChartAt (𝓡 n) x).right_inv hv.2
  have hdV := coordinateSlice_snd_hasDerivAt (variationChart V x)
    ((((variationChart_contDiffOn V x) (s, 0) hsV).contDiffAt
      ((variationChartDomain_open V x).mem_nhds hsV)).differentiableAt (by simp))
  have hdshift : HasDerivAt (fun v ↦ supportedChartShift V x η c (s, v))
      (coordinatePartialU (variationChart V x) (s, 0) + c • η s) 0 := by
    have hdη : HasDerivAt (fun v : ℝ ↦ (v * c) • η s) (c • η s) 0 := by
      convert ((hasDerivAt_id (0 : ℝ)).mul_const c).smul_const (η s) using 1 <;>
        first | rfl | simp only [one_mul]
    exact hdV.add hdη
  have hdW := hdshift.congr_of_eventuallyEq heq
  have hWs : (s, (0 : ℝ)) ∈ W.squareDomain :=
    W.square_contains ⟨hs, neg_neg_of_pos W.radius_pos, W.radius_pos⟩
  have hWcurve := (((W.square_smooth (s, 0) hWs).contMDiffAt
    (W.square_open.mem_nhds hWs)).mdifferentiableAt (by simp)).comp 0
      (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  calc
    squareVariationField W s = chartFrame x
        (deriv ((extChartAt (𝓡 n) x) ∘ W.squareFamily s) 0) (W.baseSquareCurve s) :=
      (chartFrame_curveVelocity (α := W.squareFamily s) (s := 0) hxW hWcurve).symm
    _ = chartFrame x (coordinatePartialU (variationChart V x) (s, 0) + c • η s)
        (V.baseSquareCurve s) := by rw [hdW.deriv, hbase]
    _ = chartFrame x (coordinatePartialU (variationChart V x) (s, 0))
          (V.baseSquareCurve s) + c • chartFrame x (η s) (V.baseSquareCurve s) := by
      simp only [chartFrame, map_add, map_smul]
    _ = _ := by rw [variationChart_squareVariationField V hs hx]

end PoincareConjecture.M08
