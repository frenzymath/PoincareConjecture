import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Expanding.TerminalJets
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Parametrized.LinearEquiv
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal BigOperators

universe u
namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace


private theorem linear_parameter_quadratic_bounds
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




theorem exists_terminal_parametrized_spatialJet_time_constant
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] E)
    (d : ℕ) (Z : ℕ → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
        [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
        [IsManifold (𝓡 (m + 1)) ∞ M]
        (J : Set ℝ), IsOpen J → ∀ F : RicciFlow (m + 1) M J,
        Icc (-2 : ℝ) 0 ⊆ J →
        (∀ t ∈ Icc (-2 : ℝ) 0, MetricComplete (F.metric t)) →
        (∀ t ∈ Icc (-2 : ℝ) 0, ∀ y : M,
          (F.connection t).NonnegativeCurvatureOperator y) →
        ∀ p : M,
        (∀ t ∈ Icc (-2 : ℝ) 0,
          ∀ y ∈ (F.metric 0).ball p (64 * (((m + 1 : ℕ) : ℝ) + 8)),
            (F.connection t).scalarCurvature y ≤ 4) →
        ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 →
        ∀ {U : Set E}, IsOpen U →
        ∀ {e : E → M},
          ContMDiffOn 𝓘(ℝ, E) (𝓡 (m + 1)) ∞ e U →
          (∀ y ∈ U, (mfderiv 𝓘(ℝ, E) (𝓡 (m + 1)) e y).IsInvertible) →
        ∀ {x : E}, x ∈ U →
        (F.metric 0).edist p (e x) ≤
          ENNReal.ofReal (16 * (((m + 1 : ℕ) : ℝ) + 8)) →
        (∀ v, a * ‖v‖ ^ 2 ≤ (F.metric (-δ)).parametrizedCoefficients e x v v ∧
          (F.metric (-δ)).parametrizedCoefficients e x v v ≤ b * ‖v‖ ^ 2) →
        (∀ j ≤ d,
          ‖iteratedFDeriv ℝ j ((F.metric (-δ)).parametrizedCoefficients e) x‖ ≤ Z j) →
        ∀ j ≤ d, ∀ s ∈ Icc (-δ) 0, ∀ t ∈ Icc (-δ) 0,
          ‖iteratedFDeriv ℝ j ((F.metric t).parametrizedCoefficients e) x -
            iteratedFDeriv ℝ j ((F.metric s).parametrizedCoefficients e) x‖ ≤ B * |t - s| := by
  classical
  have hLinverse : 0 < ‖L.symm.toContinuousLinearMap‖ := L.norm_symm_pos
  let Z' := fun j => ‖L.toContinuousLinearMap‖ ^ (j + 2) * Z j
  obtain ⟨B₀, hB₀, hbound⟩ :=
    exists_terminal_cylinder_spatialJet_time_constant hC hm d Z'
      (a := a / ‖L.symm.toContinuousLinearMap‖ ^ 2)
      (b := b * ‖L.toContinuousLinearMap‖ ^ 2) (by positivity) (by positivity)
  let D : ℝ := ∑ j ∈ Finset.range (d + 1), ‖L.symm.toContinuousLinearMap‖ ^ (j + 2)
  have hD : 0 ≤ D := Finset.sum_nonneg fun j _ => pow_nonneg (norm_nonneg _) _
  refine ⟨D * B₀, mul_nonneg hD hB₀, ?_⟩
  intro M _ _ _ _ _ J hJ F hsub hcomplete hoperator p hscalar
    δ hδ hδone U hU e he hi x hx hdist hell hinit j hj s hs t ht
  have hU' : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have he' := RiemannianMetric.contMDiffOn_comp_parameterEquiv L he
  have hi' : ∀ y ∈ L ⁻¹' U,
      (mfderiv (𝓡 (m + 1)) (𝓡 (m + 1)) (e ∘ L) y).IsInvertible :=
    fun y hy => (RiemannianMetric.isInvertible_mfderiv_comp_parameterEquiv_iff L e y).mpr
      (hi (L y) hy)
  have hx' : L.symm x ∈ L ⁻¹' U := by simpa using hx
  have hdist' : (F.metric 0).edist p ((e ∘ L) (L.symm x)) ≤
      ENNReal.ofReal (16 * (((m + 1 : ℕ) : ℝ) + 8)) := by
    simpa only [Function.comp_apply, L.apply_symm_apply] using hdist
  have hcoeff :
      (F.metric (-δ)).pullbackCoefficients (e ∘ L) (L.symm x) =
        RiemannianMetric.parameterBilinearEquiv L
          ((F.metric (-δ)).parametrizedCoefficients e x) := by
    change (F.metric (-δ)).parametrizedCoefficients (e ∘ L) (L.symm x) = _
    simp only [RiemannianMetric.parametrizedCoefficients_comp_parameterEquiv, L.apply_symm_apply]
  have hell' : ∀ v,
      (a / ‖L.symm.toContinuousLinearMap‖ ^ 2) * ‖v‖ ^ 2 ≤
        (F.metric (-δ)).pullbackCoefficients (e ∘ L) (L.symm x) v v ∧
      (F.metric (-δ)).pullbackCoefficients (e ∘ L) (L.symm x) v v ≤
        (b * ‖L.toContinuousLinearMap‖ ^ 2) * ‖v‖ ^ 2 := by
    intro v
    rw [hcoeff]
    exact linear_parameter_quadratic_bounds L _ ha hb hell v
  have hinit' : ∀ l ≤ d,
      ‖iteratedFDeriv ℝ l ((F.metric (-δ)).pullbackCoefficients (e ∘ L))
        (L.symm x)‖ ≤ Z' l := by
    intro l hl
    have h := (F.metric (-δ)).norm_iteratedFDeriv_parametrizedCoefficients_comp_parameterEquiv_le
      L e l (L.symm x)
    simp only [L.apply_symm_apply] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hinit l hl) (pow_nonneg (norm_nonneg _) _))
  have hEuclidean := hbound M J hJ F hsub hcomplete hoperator p hscalar
    hδ hδone hU' he' hi' hx' hdist' hell' hinit' j hj s hs t ht
  have hreturn := RiemannianMetric.norm_iteratedFDeriv_parametrizedCoefficients_sub_le_comp
    (F.metric t) (F.metric s) L e j (L.symm x)
  simp only [L.apply_symm_apply] at hreturn
  have hjD : ‖L.symm.toContinuousLinearMap‖ ^ (j + 2) ≤ D :=
    Finset.single_le_sum
      (fun l _ => pow_nonneg (norm_nonneg L.symm.toContinuousLinearMap) (l + 2))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  exact hreturn.trans ((mul_le_mul_of_nonneg_left hEuclidean
    (pow_nonneg (norm_nonneg _) _)).trans
      ((mul_le_mul_of_nonneg_right hjD (mul_nonneg hB₀ (abs_nonneg _))).trans_eq (by ring)))




theorem eventually_terminal_parametrizedJet_control_of_expanding_cylinders
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : EuclideanSpace ℝ (Fin (m + 1)) ≃L[ℝ] E)
    (d : ℕ) (Z : ℕ → ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (C : ℕ → FlowCarrier.{u} (m + 1)) (J : ℕ → Set ℝ)
        (F : ∀ k, RicciFlow (m + 1) (C k).carrier (J k))
        (p : ∀ k, (C k).carrier) (A radius : ℕ → ℝ),
        Tendsto A atTop atTop → Tendsto radius atTop atTop →
        (∀ k, IsOpen (J k)) →
        (∀ k, Icc (-A k) 0 ⊆ interior (J k)) →
        (∀ k, ∀ t ∈ Icc (-A k) 0, MetricComplete ((F k).metric t)) →
        (∀ k, ∀ t ∈ Icc (-A k) 0, ∀ y : (C k).carrier,
          ((F k).connection t).NonnegativeCurvatureOperator y) →
        (∀ k, ∀ t ∈ Icc (-A k) 0,
          ∀ y ∈ ((F k).metric 0).ball (p k) (radius k),
            ((F k).connection t).scalarCurvature y ≤ 4) →
        ∀ R : ℝ, 0 ≤ R → ∀ᶠ k in atTop,
          ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 →
          ∀ {U : Set E}, IsOpen U →
          ∀ {e : E → (C k).carrier}, ContMDiffOn 𝓘(ℝ, E) (𝓡 (m + 1)) ∞ e U →
            (∀ y ∈ U, (mfderiv 𝓘(ℝ, E) (𝓡 (m + 1)) e y).IsInvertible) →
          ∀ {x : E}, x ∈ U →
          ((F k).metric 0).edist (p k) (e x) ≤ ENNReal.ofReal R →
          (∀ v, a * ‖v‖ ^ 2 ≤
              ((F k).metric (-δ)).parametrizedCoefficients e x v v ∧
            ((F k).metric (-δ)).parametrizedCoefficients e x v v ≤ b * ‖v‖ ^ 2) →
          (∀ j ≤ d,
            ‖iteratedFDeriv ℝ j (((F k).metric (-δ)).parametrizedCoefficients e) x‖ ≤ Z j) →
          ∀ j ≤ d,
            ‖iteratedFDeriv ℝ j (((F k).metric 0).parametrizedCoefficients e) x -
              iteratedFDeriv ℝ j (((F k).metric (-δ)).parametrizedCoefficients e) x‖ ≤ B * δ := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_terminal_parametrized_spatialJet_time_constant hC hm L d Z ha hb
  refine ⟨B, hB, ?_⟩
  intro C J F p A radius hA hradius hopen hJ hcomplete hoperator hscalar R hR
  let r : ℝ := 64 * (((m + 1 : ℕ) : ℝ) + 8)
  have hr : 0 < r := by dsimp [r]; positivity
  filter_upwards [hA.eventually_ge_atTop 2, hradius.eventually_ge_atTop (R + r + 1)]
    with k hkA hkL
  intro δ hδ hδone U hU e he hi x hx hdist hell hinit j hj
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : (C k).carrier → Type _) :=
    ⟨((F k).metric 0).toRiemannianMetric⟩
  have hsub : Icc (-2 : ℝ) 0 ⊆ Icc (-A k) 0 := Icc_subset_Icc (by linarith) le_rfl
  have hlocal : ∀ t ∈ Icc (-2 : ℝ) 0,
      ∀ y ∈ ((F k).metric 0).ball (e x) r,
        ((F k).connection t).scalarCurvature y ≤ 4 := by
    intro t ht y hy
    apply hscalar k t (hsub ht) y
    have htri : ((F k).metric 0).edist (p k) y ≤
        ((F k).metric 0).edist (p k) (e x) +
          ((F k).metric 0).edist (e x) y :=
      Manifold.riemannianEDist_triangle
    have hsum : ((F k).metric 0).edist (p k) y ≤ ENNReal.ofReal (R + r) := by
      rw [ENNReal.ofReal_add hR hr.le]
      exact htri.trans (add_le_add hdist hy.le)
    have hgap : ENNReal.ofReal (R + r) < ENNReal.ofReal (R + r + 1) :=
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr (by linarith)
    exact (hsum.trans_lt hgap).trans_le
      (ENNReal.ofReal_le_ofReal (by linarith [hkL]))
  have h := hbound (C k).carrier (J k) (hopen k) (F k)
    (fun _ ht => interior_subset (hJ k (hsub ht)))
    (fun t ht => hcomplete k t (hsub ht))
    (fun t ht => hoperator k t (hsub ht)) (e x) hlocal hδ hδone hU he hi hx
    (by change Manifold.riemannianEDist (𝓡 (m + 1)) (e x) (e x) ≤ _
        rw [Manifold.riemannianEDist_self]; exact bot_le) hell hinit j hj
    (-δ) ⟨le_rfl, by linarith⟩ 0 ⟨by linarith, le_rfl⟩
  simpa only [zero_sub, neg_neg, abs_of_pos hδ] using h

end PoincareConjecture.RicciFlow
