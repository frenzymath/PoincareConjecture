import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Sequence.Coercivity.Metric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Sequence.Coercivity.Curve
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Sequence.Coercivity.Weighted
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Sequence.AdmissiblePaths
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.AncientKappaSolution

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem distance_le_backwardLLength_young (K : AncientKappaSolution 2 M)
    {τ : ℝ} (path : BackwardTimePath K.flow 0 0 τ) {C : ℝ} (hC : 0 < C) :
    ((K.flow.metric 0).edist (path.curve 0) (path.curve τ)).toReal ≤
      (backwardLLength K.flow 0 0 τ path.curve + 2 * C ^ 2 * Real.sqrt τ) / (2 * C) := by
  let g := K.flow.metric 0
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 2) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply g.toReal_edist_endpoints_le_of_interior_bound path.ordered path.continuous
  intro a b ha hab hb
  have hsub : Icc a b ⊆ Ioo 0 τ :=
    fun s hs => ⟨ha.trans_le hs.1, hs.2.trans_lt hb⟩
  have hspeed := (g.continuousOn_speed_of_contMDiffOn_one isOpen_Ioo path.regular).mono hsub
  have hd := g.edist_le_ofReal_integral_speed hab (path.regular.mono hsub) hspeed
  have hn : 0 ≤ ∫ s in a..b,
      g.tangentNorm (path.curve s) (curveVelocity (n := 2) path.curve s) :=
    intervalIntegral.integral_nonneg hab (fun _ _ => Real.sqrt_nonneg _)
  have hd' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hd
  dsimp only [curveVelocity] at hn
  rw [ENNReal.toReal_ofReal hn] at hd'
  apply hd'.trans
  apply Poincare.Analysis.integral_speed_le_weighted_action ha hab hb.le hC path.l_integrable
    (fun s hs => K.backwardLIntegrand_nonneg path.curve hs.1) hspeed
  intro s hs
  have hss : 0 ≤ s := (hsub hs).1.le
  have hR := (K.flow.connection (0 - s)).scalar_nonnegative_of_nonnegative_curvatureOperator
    (path.curve s) (K.nonnegative_curvature_operator (0 - s) (by linarith) (path.curve s))
  have hg := K.surface_metric_monotone (s := 0 - s) (t := 0) (by linarith) le_rfl
    (path.curve s) (curveVelocity (n := 2) path.curve s)
  have hnorm : 0 ≤ g.inner (path.curve s) (curveVelocity (n := 2) path.curve s)
      (curveVelocity (n := 2) path.curve s) :=
    show 0 ≤ inner ℝ (curveVelocity (n := 2) path.curve s)
      (curveVelocity (n := 2) path.curve s) from real_inner_self_nonneg
  change Real.sqrt s * (Real.sqrt (g.inner (path.curve s)
    (curveVelocity (n := 2) path.curve s) (curveVelocity (n := 2) path.curve s))) ^ 2 ≤ _
  rw [Real.sq_sqrt hnorm]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg s)
  change g.inner _ _ _ ≤ _
  linarith


theorem distance_sq_div_sqrt_le_backwardLLength (K : AncientKappaSolution 2 M)
    {τ : ℝ} (path : BackwardTimePath K.flow 0 0 τ) :
    ((K.flow.metric 0).edist (path.curve 0) (path.curve τ)).toReal ^ 2 /
      (2 * Real.sqrt τ) ≤ backwardLLength K.flow 0 0 τ path.curve := by
  let d := ((K.flow.metric 0).edist (path.curve 0) (path.curve τ)).toReal
  have hd : 0 ≤ d := ENNReal.toReal_nonneg
  have hs : 0 < Real.sqrt τ := Real.sqrt_pos.2 path.ordered
  by_cases hd0 : d = 0
  · change d ^ 2 / (2 * Real.sqrt τ) ≤ _
    simpa only [hd0, zero_pow (by decide : 2 ≠ 0), zero_div] using
      K.backwardLLength_nonneg path.curve path.ordered.le
  have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hd0)
  let C := d / (2 * Real.sqrt τ)
  have hC : 0 < C := div_pos hdpos (by positivity)
  have hCd : C * (2 * Real.sqrt τ) = d := by dsimp [C]; field_simp
  have h := (le_div_iff₀ (by positivity : 0 < 2 * C)).mp
    (K.distance_le_backwardLLength_young path hC)
  change d * (2 * C) ≤ _ at h
  have hmid : C * d ≤ backwardLLength K.flow 0 0 τ path.curve := by nlinarith [hCd]
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt τ)).mpr
  change d ^ 2 ≤ _
  calc
    d ^ 2 = (C * d) * (2 * Real.sqrt τ) := by rw [← hCd]; ring
    _ ≤ backwardLLength K.flow 0 0 τ path.curve * (2 * Real.sqrt τ) :=
      mul_le_mul_of_nonneg_right hmid (by positivity)


theorem distance_sq_div_le_reducedLength (K : AncientKappaSolution 2 M)
    (p q : M) {τ : ℝ} (hτ : 0 < τ) :
    ((K.flow.metric 0).edist p q).toReal ^ 2 / (4 * τ) ≤ reducedLength K.flow 0 p q τ := by
  rw [reducedLength, dif_pos hτ]
  have hnonempty : Set.Nonempty {L : ℝ |
      ∃ path : BackwardTimePath K.flow 0 0 τ,
        path.curve 0 = p ∧ path.curve τ = q ∧ L = backwardLLength K.flow 0 0 τ path.curve} := by
    obtain ⟨path, hp, hq⟩ := K.exists_backwardTimePath_surface p q hτ
    exact ⟨_, path, hp, hq, rfl⟩
  have hbound : ((K.flow.metric 0).edist p q).toReal ^ 2 / (2 * Real.sqrt τ) ≤
      sInf {L : ℝ | ∃ path : BackwardTimePath K.flow 0 0 τ,
        path.curve 0 = p ∧ path.curve τ = q ∧ L = backwardLLength K.flow 0 0 τ path.curve} := by
    apply le_csInf hnonempty
    rintro L ⟨path, hp, hq, rfl⟩
    simpa only [hp, hq] using K.distance_sq_div_sqrt_le_backwardLLength path
  have heq : ((K.flow.metric 0).edist p q).toReal ^ 2 / (4 * τ) =
      (((K.flow.metric 0).edist p q).toReal ^ 2 / (2 * Real.sqrt τ)) / (2 * Real.sqrt τ) := by
    rw [div_div]
    congr 1
    nlinarith [Real.sq_sqrt hτ.le]
  rw [heq]
  exact div_le_div_of_nonneg_right hbound (by positivity)


theorem reducedLength_sublevel_subset_closedBall (K : AncientKappaSolution 2 M)
    (p : M) {τ : ℝ} (hτ : 0 < τ) (A : ℝ) :
    {q | reducedLength K.flow 0 p q τ ≤ A} ⊆
      {q | (K.flow.metric 0).edist p q ≤ ENNReal.ofReal (Real.sqrt (4 * τ * A))} := by
  intro q hq
  have hsq := (div_le_iff₀ (by positivity : 0 < 4 * τ)).mp
    ((K.distance_sq_div_le_reducedLength p q hτ).trans hq)
  have hd : ((K.flow.metric 0).edist p q).toReal ≤ Real.sqrt (4 * τ * A) :=
    Real.le_sqrt_of_sq_le (by simpa only [mul_comm A] using hsq)
  exact (ENNReal.ofReal_toReal ((K.flow.metric 0).edist_ne_top p q)).symm.le.trans
    (ENNReal.ofReal_le_ofReal hd)


theorem isCompact_closure_reducedLength_sublevel (K : AncientKappaSolution 2 M)
    (p : M) {τ : ℝ} (hτ : 0 < τ) (A : ℝ) :
    IsCompact (closure {q | reducedLength K.flow 0 p q τ ≤ A}) := by
  have hc := (K.flow.metric 0).isCompact_closedBall_of_metricComplete
    (K.complete 0 le_rfl) p (Real.sqrt (4 * τ * A))
  exact hc.of_isClosed_subset isClosed_closure
    (closure_minimal (K.reducedLength_sublevel_subset_closedBall p hτ A) hc.isClosed)

end PoincareConjecture.AncientKappaSolution
