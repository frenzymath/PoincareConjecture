import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_4_SliceVariation
import PoincareConjecture.Proofs.M14.Sec6_5_HessianIndexComparison
import PoincareConjecture.Proofs.M14.Sec6_5_AdaptedIndexIntegral
import PoincareConjecture.Proofs.M14.Sec6_5_HarnackIntegral
import PoincareConjecture.Proofs.M09.LocalMinimumHessian










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology BigOperators intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b : ℝ} {x y : G.Point} {p : M14BackwardPath G T a b x y}
  {R : M14SquareRootPath G p}




theorem sliceMinimum_pullback_index_nonneg
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {B : ℝ} (hB : M14BackwardLAction G p < B) (hp : M14IsMinimizing p)
    (hmin : ∀ (z : G.Point) (q : M14BackwardPath G T a b x z),
      M14BackwardLAction G q < B → M14BackwardLAction G p ≤ M14BackwardLAction G q)
    {Y : ∀ s, G.Horizontal (R.curve s)}
    (EY : M14PullbackExtension G R.curve (M14SqrtParameterInterval a b) Y)
    (hleft : Y (Real.sqrt a) = 0) :
    0 ≤ ∫ s in Real.sqrt a..Real.sqrt b, M14.pullbackIndexPairDensity R EY EY s := by
  have hY := M14.pullbackExtension_field_contMDiffOn EY (R.smooth.mono R.interval_subset)
  obtain ⟨V, hfix, hfield, _⟩ :=
    M14.exists_initialFixed_variation_of_smooth_horizontalField R hM12 Y hY hleft
  obtain ⟨D⟩ := M14.exists_variationDerivativeData V
  have hlocal := sliceMinimum_variationAction_isLocalMin hM12 hB hmin V hfix
  have hP : IsOpen V.parameterDomain := V.parameterDomain_eq ▸ isOpen_Ioo
  have hzero : (0 : ℝ) ∈ V.parameterDomain := by
    rw [V.parameterDomain_eq]
    exact ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  have hcont := (M14.variationAction_contDiffOn hM12 V).continuousOn.continuousAt
    (hP.mem_nhds hzero)
  have hnonneg := M09.localMin_secondDeriv_nonneg (M14VariationAction V) 0 hcont hlocal
  obtain ⟨_, d, hd, heq⟩ := M14.secondVariationIdentity_of_squareEuler
    hCoordinates hM04 hM12 V D (fun _ hs W =>
      M14.squareRootEulerResidual_eq_zero_of_minimizing hCoordinates hM12 hp
        D.base_extension hs W)
  rw [hd.deriv, heq, M14.secondVariationBoundaryTerm_initialFixed V D hfix,
    sliceMinimum_terminal_velocity_eq_zero hCoordinates hM12 hB hp hmin,
    map_zero, zero_apply, zero_add,
    M14.secondVariationIndexForm_eq_of_field V D EY hfield] at hnonneg
  exact hnonneg




theorem sliceMinimum_scalar_reducedLength_le_dimension
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {p : M14BackwardPath G T 0 b x y} (R : M14SquareRootPath G p)
    {B : ℝ} (hB : M14BackwardLAction G p < B) (hp : M14IsMinimizing p)
    (hmin : ∀ (z : G.Point) (q : M14BackwardPath G T 0 b x z),
      M14BackwardLAction G q < B → M14BackwardLAction G p ≤ M14BackwardLAction G q) :
    b * horizontalScalarCurvature G.leafwise (R.curve (Real.sqrt b)) +
      M14BackwardLAction G p / (2 * Real.sqrt b) ≤ (n : ℝ) := by
  classical
  have hb : 0 < b := p.tau_lt
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  obtain ⟨E⟩ := M14.exists_squareRoot_velocity_extension R
  have hEuler : ∀ s ∈ Ioo 0 (Real.sqrt b), ∀ W,
      M14SquareRootEulerResidual G R E s W = 0 := by
    intro s h W
    apply M14.squareRootEulerResidual_eq_zero_of_minimizing hCoordinates hM12 hp E
    simpa only [M14SqrtParameterInterval, Real.sqrt_zero] using Ioo_subset_Icc_self h
  have hK := M14.squareRoot_weightedHarnack_intervalIntegrable hM12 R E
    (by simpa only [Real.sqrt_zero] using hEuler)
  obtain ⟨P, hP, horth, _⟩ := M14.exists_horizontalUnitAdaptedFrame R hM04 hM12
  let EP := fun i => Classical.choose (hP i).equation
  have hindex (i : Fin n) :
      0 ≤ ∫ s in Real.sqrt 0..Real.sqrt b, M14.pullbackIndexPairDensity R
        (M14.horizontalAdaptedExtension (EP i)) (M14.horizontalAdaptedExtension (EP i)) s := by
    apply sliceMinimum_pullback_index_nonneg hCoordinates hM04 hM12 hB hp hmin
    exact (M14.horizontalAdaptedField_endpoints
      (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt)).1
  have hsum := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hindex i)
  rw [M14.integral_adaptedPullbackIndex R hM04 hM12 P hP EP horth hK,
    Real.sqrt_zero, sub_zero, Real.sq_sqrt hb.le] at hsum
  have hshift :
      (∫ t in 0..b, Real.sqrt t * (Real.sqrt t - Real.sqrt 0) ^ 2 *
        M14GeneralizedHarnackDensity G p
          (fun r => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
            (p.curve r)) t) = M14GeneralizedKIntegral G p
        (fun r => M14BackwardTimeDerivative G (horizontalScalarCurvature G.leafwise)
          (p.curve r)) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hb.le
    intro t ht
    simp only [Real.sqrt_zero, sub_zero, Real.sq_sqrt ht.1.le]
    ring
  have hH := M14.squareRoot_harnackIntegral_zero_start hM12 R E hEuler
  rw [M14.squareHarnackPrimitive,
    sliceMinimum_terminal_velocity_eq_zero hCoordinates hM12 hB hp hmin,
    map_zero, mul_zero, zero_div, add_zero] at hH
  simp only [Real.sqrt_zero, sub_zero] at hshift hsum
  rw [hshift, hH] at hsum
  have hscaled := mul_nonneg hsum hs.le
  have heq :
      ((n : ℝ) / Real.sqrt b -
        2 * Real.sqrt b * horizontalScalarCurvature G.leafwise (R.curve (Real.sqrt b)) -
        (M14BackwardLAction G p / 2 - Real.sqrt b ^ 3 *
          horizontalScalarCurvature G.leafwise (R.curve (Real.sqrt b))) / b) * Real.sqrt b =
      (n : ℝ) - b * horizontalScalarCurvature G.leafwise (R.curve (Real.sqrt b)) -
        M14BackwardLAction G p / (2 * Real.sqrt b) := by
    set s := Real.sqrt b
    generalize horizontalScalarCurvature G.leafwise (R.curve s) = rho
    generalize M14BackwardLAction G p = L
    have hs0 : s ≠ 0 := hs.ne'
    have hs2 : b = s ^ 2 := (Real.sq_sqrt hb.le).symm
    rw [hs2]
    field_simp [hs0]
    ring
  rw [heq] at hscaled
  linarith

end PoincareConjecture.Proofs.M46
