import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.TerminalJets
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Parametrized.LinearEquiv








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal BigOperators

namespace PoincareConjecture.RawAncientSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

variable (C : ℕ → FlowCarrier.{0} 3)
  (F : ∀ k, RicciFlow 3 (C k).carrier (Iic 0)) (p : ∀ k, (C k).carrier)

private theorem parameter_quadratic_bounds
    {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [Nontrivial E']
    (L : E' ≃L[ℝ] E) (T : E →L[ℝ] E →L[ℝ] ℝ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hT : ∀ v, a * ‖v‖ ^ 2 ≤ T v v ∧ T v v ≤ b * ‖v‖ ^ 2)
    (v : E') :
    (a / ‖L.symm.toContinuousLinearMap‖ ^ 2) * ‖v‖ ^ 2 ≤
        RiemannianMetric.parameterBilinearEquiv L T v v ∧
      RiemannianMetric.parameterBilinearEquiv L T v v ≤
        (b * ‖L.toContinuousLinearMap‖ ^ 2) * ‖v‖ ^ 2 := by
  have hinv : 0 < ‖L.symm.toContinuousLinearMap‖ := L.norm_symm_pos
  have hvlower : ‖v‖ ≤ ‖L.symm.toContinuousLinearMap‖ * ‖L v‖ := by
    simpa using L.symm.toContinuousLinearMap.le_opNorm (L v)
  have hvlower₂ : ‖v‖ ^ 2 ≤ ‖L.symm.toContinuousLinearMap‖ ^ 2 * ‖L v‖ ^ 2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg v) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hvlower
  have hvupper₂ : ‖L v‖ ^ 2 ≤ ‖L.toContinuousLinearMap‖ ^ 2 * ‖v‖ ^ 2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg (L v)) (mul_nonneg (norm_nonneg _) (norm_nonneg v))).mpr
        (L.toContinuousLinearMap.le_opNorm v)
  simp only [RiemannianMetric.parameterBilinearEquiv_apply]
  constructor
  · apply le_trans _ (hT (L v)).1
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (sq_pos_of_pos hinv)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hvlower₂ ha.le]
  · exact (hT (L v)).2.trans ((mul_le_mul_of_nonneg_left hvupper₂ hb).trans_eq (by ring))




theorem exists_eventually_terminal_parametrizedJet_time_constant
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hc : ∀ k t, t ≤ 0 → MetricComplete ((F k).metric t))
    (hop : ∀ k t, t ≤ 0 → ∀ x, ((F k).connection t).NonnegativeCurvatureOperator x)
    (radius : ℕ → ℝ) (hradius : Tendsto radius atTop atTop)
    (hbound : ∀ k t, t ≤ 0 → ∀ x ∈ ((F k).metric 0).ball (p k) (radius k),
      |((F k).connection t).curvatureTensorNorm x| ≤ 4)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] E)
    (d : ℕ) (Z : ℕ → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, 0 ≤ R → ∀ᶠ k in atTop,
      ∀ {U : Set E}, IsOpen U →
      ∀ {e : E → (C k).carrier}, ContMDiffOn 𝓘(ℝ, E) (𝓡 3) ∞ e U →
      (∀ y ∈ U, (mfderiv 𝓘(ℝ, E) (𝓡 3) e y).IsInvertible) →
      ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 →
      ∀ {x : E}, x ∈ U →
      ((F k).metric 0).edist (p k) (e x) ≤ ENNReal.ofReal R →
      (∀ v, a * ‖v‖ ^ 2 ≤ ((F k).metric (-δ)).parametrizedCoefficients e x v v ∧
        ((F k).metric (-δ)).parametrizedCoefficients e x v v ≤ b * ‖v‖ ^ 2) →
      (∀ j ≤ d,
        ‖iteratedFDeriv ℝ j (((F k).metric (-δ)).parametrizedCoefficients e) x‖ ≤ Z j) →
      ∀ j ≤ d,
        ‖iteratedFDeriv ℝ j (((F k).metric 0).parametrizedCoefficients e) x -
          iteratedFDeriv ℝ j (((F k).metric (-δ)).parametrizedCoefficients e) x‖ ≤ B * δ := by
  classical
  have hLinverse : 0 < ‖L.symm.toContinuousLinearMap‖ := L.norm_symm_pos
  let Z' := fun j => ‖L.toContinuousLinearMap‖ ^ (j + 2) * Z j
  obtain ⟨B₀, hB₀, htime⟩ := exists_eventually_terminal_spatialJet_time_constant C F p P
    hc hop radius hradius hbound d Z'
    (a := a / ‖L.symm.toContinuousLinearMap‖ ^ 2)
    (b := b * ‖L.toContinuousLinearMap‖ ^ 2) (by positivity) (by positivity)
  let D : ℝ := ∑ j ∈ Finset.range (d + 1), ‖L.symm.toContinuousLinearMap‖ ^ (j + 2)
  have hD : 0 ≤ D := Finset.sum_nonneg fun j _ => pow_nonneg (norm_nonneg _) _
  refine ⟨D * B₀, mul_nonneg hD hB₀, ?_⟩
  intro R hR
  filter_upwards [htime R hR] with k hk
  intro U hU e he hi δ hδ hδone x hx hdist hell hinit j hj
  have hU' : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have he' := RiemannianMetric.contMDiffOn_comp_parameterEquiv L he
  have hi' : ∀ y ∈ L ⁻¹' U, (mfderiv (𝓡 3) (𝓡 3) (e ∘ L) y).IsInvertible :=
    fun y hy => (RiemannianMetric.isInvertible_mfderiv_comp_parameterEquiv_iff L e y).mpr
      (hi (L y) hy)
  have hx' : L.symm x ∈ L ⁻¹' U := by simpa using hx
  have hdist' : ((F k).metric 0).edist (p k) ((e ∘ L) (L.symm x)) ≤
      ENNReal.ofReal R := by simpa only [Function.comp_apply, L.apply_symm_apply] using hdist
  have hcoeff : ((F k).metric (-δ)).pullbackCoefficients (e ∘ L) (L.symm x) =
      RiemannianMetric.parameterBilinearEquiv L
        (((F k).metric (-δ)).parametrizedCoefficients e x) := by
    change ((F k).metric (-δ)).parametrizedCoefficients (e ∘ L) (L.symm x) = _
    simp only [RiemannianMetric.parametrizedCoefficients_comp_parameterEquiv, L.apply_symm_apply]
  have hell' : ∀ v,
      (a / ‖L.symm.toContinuousLinearMap‖ ^ 2) * ‖v‖ ^ 2 ≤
        ((F k).metric (-δ)).pullbackCoefficients (e ∘ L) (L.symm x) v v ∧
      ((F k).metric (-δ)).pullbackCoefficients (e ∘ L) (L.symm x) v v ≤
        (b * ‖L.toContinuousLinearMap‖ ^ 2) * ‖v‖ ^ 2 := by
    intro v
    rw [hcoeff]
    exact parameter_quadratic_bounds L _ ha hb hell v
  have hinit' : ∀ l ≤ d,
      ‖iteratedFDeriv ℝ l (((F k).metric (-δ)).pullbackCoefficients (e ∘ L))
        (L.symm x)‖ ≤ Z' l := by
    intro l hl
    have h := ((F k).metric (-δ)).norm_iteratedFDeriv_parametrizedCoefficients_comp_parameterEquiv_le
      L e l (L.symm x)
    simp only [L.apply_symm_apply] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hinit l hl) (pow_nonneg (norm_nonneg _) _))
  have hEuclidean := hk hU' he' hi' hδ hδone hx' hdist' hell' hinit' j hj
  have hreturn := RiemannianMetric.norm_iteratedFDeriv_parametrizedCoefficients_sub_le_comp
    ((F k).metric 0) ((F k).metric (-δ)) L e j (L.symm x)
  simp only [L.apply_symm_apply] at hreturn
  have hjD : ‖L.symm.toContinuousLinearMap‖ ^ (j + 2) ≤ D :=
    Finset.single_le_sum (fun l _ => pow_nonneg (norm_nonneg L.symm.toContinuousLinearMap) (l + 2))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  exact hreturn.trans ((mul_le_mul_of_nonneg_left hEuclidean
    (pow_nonneg (norm_nonneg _) _)).trans
      ((mul_le_mul_of_nonneg_right hjD (mul_nonneg hB₀ hδ.le)).trans_eq (by ring)))

end PoincareConjecture.RawAncientSequence
