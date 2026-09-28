import PoincareConjecture.Proofs.M09.ChartFieldDerivative
import PoincareConjecture.Proofs.M09.VelocityRestriction
import PoincareConjecture.Proofs.M09.FamilySquareVelocity








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T b τmax : ℝ}

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem initialFixedVariation_acceleration_zero {P : BackwardTimePath F T 0 b}
    (V : InitialFixedLVariation F T 0 b P) (D : LVariationDerivativeData V.toLVariation)
    (h0 : (0 : ℝ) ∈ sqrtParameterInterval 0 b) :
    variationEndpointAcceleration V.toLVariation D 0 h0 = 0 := by
  let I := V.toLVariation.parameterDomain
  let η := V.squareFamily 0
  have hI : IsOpen I := isOpen_Ioo
  have hz : (0 : ℝ) ∈ I := ⟨neg_lt_zero.mpr V.radius_pos, V.radius_pos⟩
  have hc (r : ℝ) (hr : r ∈ I) : η r = P.curve 0 := by
    have h := V.square_agrees 0 h0 r hr
    simpa only [zero_pow two_ne_zero, V.fixed_left r hr] using h
  have hη : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ η I :=
    V.square_smooth.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
      (fun _ hr ↦ V.square_contains ⟨h0, hr⟩)
  have hd (r : ℝ) (hr : r ∈ I) : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) η r :=
    (hη.contMDiffAt (hI.mem_nhds hr)).mdifferentiableAt (by simp)
  have hv (r : ℝ) (hr : r ∈ I) : curveVelocityWithin (n := n) η I r = 0 := by
    have heq : η =ᶠ[𝓝 r] fun _ ↦ P.curve 0 := by
      filter_upwards [hI.mem_nhds hr] with t ht
      exact hc t ht
    rw [curveVelocityWithin_eq_curveVelocity η I r (hI.uniqueDiffOn r hr) (hd r hr)]
    have h := curveVelocity_congr_of_eventuallyEq (n := n) heq
    simpa only [curveVelocity, mfderiv_const, zero_apply] using h
  have hchart (r : ℝ) (hr : r ∈ I ∩ I) :
      η r ∈ (chartAt E (P.curve 0)).source := by
    rw [hc r hr.1]
    exact mem_chart_source E (P.curve 0)
  have hrep (r : ℝ) (hr : r ∈ I ∩ I) :
      chartVectorField (P.curve 0) 0 (η r) = curveVelocityWithin (n := n) η I r := by
    rw [hv r hr.1]
    exact (mfderiv (𝓡 n) (𝓡 n) (chartAt E (P.curve 0)) (η r)).inverse.map_zero
  have h := pullbackCovariantDerivative_chart_field_zero F (fun _ ↦ T) (P.curve 0)
    η (curveVelocityWithin (n := n) η I) I I (D.endpoint_extension 0 h0)
    0 hz hI hz (hI.uniqueDiffOn 0 hz) (hd 0 hz) (fun _ ↦ (0 : E)) contDiffOn_const
    hchart hrep 0 (hasDerivAt_const 0 (0 : E)) rfl
  simpa only [variationEndpointAcceleration, zero_pow two_ne_zero, sub_zero,
    chartVectorField, VectorField.mpullback, map_zero] using h

set_option backward.isDefEq.respectTransparency false in
theorem initialFixedVariation_secondBoundary {P : BackwardTimePath F T 0 b}
    (hb : 0 < b) (V : InitialFixedLVariation F T 0 b P)
    (D : LVariationDerivativeData V.toLVariation) :
    secondVariationBoundaryTerm V.toLVariation D =
      (F.metric (T - b)).inner (V.toLVariation.baseSquareCurve (Real.sqrt b))
        (curveVelocityWithin V.toLVariation.baseSquareCurve (sqrtParameterInterval 0 b)
          (Real.sqrt b))
        (variationEndpointAcceleration V.toLVariation D (Real.sqrt b)
          ⟨Real.sqrt_le_sqrt hb.le, le_rfl⟩) := by
  have hzero (s : ℝ) (hs : s ∈ sqrtParameterInterval 0 b) (heq : s = 0) :
      variationEndpointAcceleration V.toLVariation D s hs = 0 := by
    subst s
    exact initialFixedVariation_acceleration_zero V D hs
  unfold secondVariationBoundaryTerm
  dsimp only
  rw [hzero (Real.sqrt 0) _ Real.sqrt_zero, map_zero, sub_zero, Real.sq_sqrt hb.le]

set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_initialFixedVariation_secondBoundary {p : M}
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (V : InitialFixedLVariation F T 0 b (A.path Z b hb hmax))
    (D : LVariationDerivativeData V.toLVariation)
    (hbase : V.toLVariation.baseSquareCurve = A.squareFamily Z) :
    secondVariationBoundaryTerm V.toLVariation D =
      (2 * Real.sqrt b) * (F.metric (T - b)).inner (A.gamma Z b)
        (curveVelocity (A.gamma Z) b)
        (variationEndpointAcceleration V.toLVariation D (Real.sqrt b)
          ⟨Real.sqrt_le_sqrt hb.le, le_rfl⟩) := by
  let c := Real.sqrt b
  have hc : 0 < c := Real.sqrt_pos.mpr hb
  have hsmax : c < Real.sqrt τmax := Real.sqrt_lt_sqrt hb.le hmax
  have hKd : UniqueDiffOn ℝ (sqrtParameterInterval 0 b) := by
    simpa only [sqrtParameterInterval, Real.sqrt_zero] using uniqueDiffOn_Icc hc
  have hcK : c ∈ sqrtParameterInterval 0 b := ⟨Real.sqrt_le_sqrt hb.le, le_rfl⟩
  have hβd := (lExponentialFamily_squareSlice_contMDiffAt A Z c
    ⟨hc.le, hsmax⟩).mdifferentiableAt (by simp)
  have hv : (curveVelocityWithin (n := n) V.toLVariation.baseSquareCurve
      (sqrtParameterInterval 0 b) c : E) = (2 * c) • curveVelocity (A.gamma Z) b := by
    rw [hbase, curveVelocityWithin_eq_curveVelocity (A.squareFamily Z)
      (sqrtParameterInterval 0 b) c (hKd c hcK) hβd,
      lExponentialFamily_square_velocity_eq A Z c ⟨hc, hsmax⟩]
    rw [show c ^ 2 = b from Real.sq_sqrt hb.le]
  have hp : V.toLVariation.baseSquareCurve c = A.gamma Z b := by
    rw [hbase, A.square_agrees Z c ⟨hc.le, hsmax⟩, show c ^ 2 = b from Real.sq_sqrt hb.le]
  rw [initialFixedVariation_secondBoundary hb V D]
  change (F.metric (T - b)).inner (V.toLVariation.baseSquareCurve c) _ _ = _
  rw [hv, hp, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]

end PoincareConjecture.Proofs.M09
