import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.PotentialLimit.Growth
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.PotentialLimit.Pullback
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.Coverage
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.MetricComparison

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.GradientShrinkingSolitonData

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem exists_normalizedPotential_value_gradient_ball_bound
    (S : GradientShrinkingSolitonData 3 M) (hD : S.connection.CurvatureTensorCalculus)
    (r : ℝ) (hr : 0 ≤ r) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ q : M, 1 ≤ S.potentialGradientScale q →
      ∀ x : M, (S.metric.edist q x).toReal ≤ r →
        |S.normalizedPotential q x| ≤ B ∧
          S.metric.tangentNorm x (S.connection.gradient (S.normalizedPotential q) x) ≤ B := by
  obtain ⟨C, hC, hvalue⟩ := S.exists_normalizedPotential_ball_bound
  obtain ⟨K, hK, hcurv⟩ := S.bounded_curvature
  obtain ⟨H, hH⟩ := S.exists_hamilton_conservation_threeDimensional hD
  let A := r + C * r ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let B := Real.sqrt (1 + A + 6 * K)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = 1 + A + 6 * K := Real.sq_sqrt (by positivity)
  refine ⟨max A B, le_max_of_le_right hB, fun q hq x hx => ?_⟩
  have hval : |S.normalizedPotential q x| ≤ A := hvalue q hq r hr x hx
  refine ⟨hval.trans (le_max_left _ _), le_trans ?_ (le_max_right _ _)⟩
  have ha : 0 < S.potentialGradientScale q := lt_of_lt_of_le zero_lt_one hq
  have hscalar (y : M) : |S.connection.scalarCurvature y| ≤ 3 * K :=
    (S.connection.abs_scalarCurvature_le_curvatureTensorNorm_sharp y).trans
      (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hcurv y)) (by norm_num))
  have hdiff : S.potential x - S.potential q ≤ A * S.potentialGradientScale q := by
    have h := (le_abs_self (S.normalizedPotential q x)).trans hval
    exact (div_le_iff₀ ha).mp h
  have henergy : S.potentialGradientScale x ^ 2 ≤
      S.potentialGradientScale q ^ 2 + A * S.potentialGradientScale q + 6 * K := by
    have hxH := hH x
    have hqH := hH q
    rw [← S.potentialGradientScale_sq] at hxH hqH
    linarith [(abs_le.mp (hscalar q)).2, (abs_le.mp (hscalar x)).1]
  have ha2 : 1 ≤ S.potentialGradientScale q ^ 2 := by nlinarith
  have hAa : A * S.potentialGradientScale q ≤ A * S.potentialGradientScale q ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) hA
  have hKa : 6 * K ≤ 6 * K * S.potentialGradientScale q ^ 2 :=
    le_mul_of_one_le_right (by positivity) ha2
  have hsq : S.potentialGradientScale x ^ 2 ≤
      (B * S.potentialGradientScale q) ^ 2 := by
    nlinarith [hBsq]
  have hg : S.potentialGradientScale x ≤ B * S.potentialGradientScale q := by
    nlinarith [S.potentialGradientScale_nonneg x, mul_nonneg hB ha.le]
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨S.metric.toRiemannianMetric⟩
  rw [S.gradient_normalizedPotential]
  change ‖(S.potentialGradientScale q)⁻¹ • S.connection.gradient S.potential x‖ ≤ B
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
  change (S.potentialGradientScale q)⁻¹ * S.potentialGradientScale x ≤ B
  rw [mul_comm, ← div_eq_mul_inv]
  exact (div_le_iff₀ ha).mpr hg

end PoincareConjecture.GradientShrinkingSolitonData

namespace PoincareConjecture.ShrinkingSolitonFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space
attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S) {q : ℕ → M}
  (L : AncientPointedGeometricConvergence
    (fun _ => AncientRescalingSequence.smallRescalingCarrier (M := M))
    (fun _ => G.unscaledSourceFlow.shrink.metric)
    (fun k => equivShrink M (q k)) 1)

theorem unscaledOriginalEmbedding_tangentNorm_eventually_le
    (K : Set L.limitCarrier.carrier) (hK : IsCompact K) :
    ∀ᶠ k in atTop, K ⊆ L.exhaustion k ∧
      ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
        S.metric.tangentNorm (G.unscaledOriginalEmbedding L k x)
          (mfderiv (𝓡 3) (𝓡 3) (G.unscaledOriginalEmbedding L k) x v) ≤
            2 * (L.limitFlow.metric 0).tangentNorm x v := by
  let W := L.window (C := fun _ => AncientRescalingSequence.smallRescalingCarrier (M := M))
    (fun _ => G.unscaledSourceFlow.shrink)
    (J := fun _ => Iio 1) (T := 1)
    (a := -1) (b := 1 / 2) (by norm_num) (by norm_num) 0
    (fun _ _ ht => lt_trans ht.2 (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨j, hj⟩ := W.exists_exhaustion_superset hK
  filter_upwards [W.eventually_pullback_tangentNorm_bounds hK
    (t := 0) (by constructor <;> norm_num) (C := 2) (by norm_num),
    eventually_ge_atTop j] with k hk hjk
  have hinc : K ⊆ L.exhaustion k := hj.trans (W.exhaustion_monotone hjk)
  refine ⟨hinc, fun x hx v => ?_⟩
  change Real.sqrt (S.metric.inner _ _ _) ≤ _
  rw [G.unscaledOriginalEmbedding_inner L k x (hinc hx) v v]
  exact (hk x hx v).1

theorem unscaledOriginalEmbedding_eventually_bounded_distance
    (hcomplete : L.limitCarrier.metricComplete (L.limitFlow.metric 0))
    (K : Set L.limitCarrier.carrier) (hK : IsCompact K) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ k in atTop, ∀ x ∈ K,
      (S.metric.edist (q (L.subsequence k)) (G.unscaledOriginalEmbedding L k x)).toReal ≤ R := by
  let g := L.limitFlow.metric 0
  let : PreconnectedSpace L.limitCarrier.carrier := ⟨L.limitCarrier.connected.isPreconnected⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : L.limitCarrier.carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨b, hb⟩ := hK.exists_bound_of_continuousOn
    (g.continuous_toReal_edist L.base).continuousOn
  let r := |b| + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hKr : K ⊆ g.ball L.base r := by
    intro x hx
    have hdist : (g.edist L.base x).toReal < r := by
      have hh := hb x hx
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] at hh
      exact hh.trans_lt (by dsimp [r]; linarith [le_abs_self b])
    change g.edist L.base x < ENNReal.ofReal r
    rw [← ENNReal.ofReal_toReal (g.edist_ne_top L.base x)]
    exact ENNReal.ofReal_lt_ofReal_iff hr |>.2 hdist
  have hcompact : IsCompact (closure (g.ball L.base r)) :=
    g.isCompact_closure_ball_of_metricComplete hcomplete L.base r
  refine ⟨2 * r, by positivity, ?_⟩
  filter_upwards [G.unscaledOriginalEmbedding_tangentNorm_eventually_le L
    (closure (g.ball L.base r)) hcompact] with k hk x hx
  let f := G.unscaledOriginalEmbedding L k
  obtain ⟨γ, hγ0, hγ1, hγ, hlen, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt (hKr hx) zero_lt_one
  have hmap : MapsTo γ (Icc (0 : ℝ) 1) (g.ball L.base r) := by
    intro t ht
    exact ((Manifold.riemannianEDist_le_pathELength
      (hγ.contMDiffOn.mono (Icc_subset_Icc_right ht.2)) hγ0 rfl ht.1).trans
        (Manifold.pathELength_mono le_rfl ht.2)).trans_lt hlen
  have hf (y : L.limitCarrier.carrier) (hy : y ∈ g.ball L.base r) :
      ContMDiffAt (𝓡 3) (𝓡 3) 1 f y :=
    ((G.unscaledOriginalEmbedding_contMDiffOn L k).contMDiffAt
      ((L.exhaustion_open k).mem_nhds (hk.1 (subset_closure hy)))).of_le (by simp)
  have hreg : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (f ∘ γ) (Icc 0 1) := by
    intro t ht
    exact ((hf (γ t) (hmap ht)).comp t (hγ t)).contMDiffWithinAt
  have hdist : S.metric.edist (f L.base) (f x) ≤
      S.metric.pathELength (f ∘ γ) 0 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨S.metric.toRiemannianMetric⟩
    exact Manifold.riemannianEDist_le_pathELength hreg
      (congrArg f hγ0) (congrArg f hγ1) zero_le_one
  have hlength := g.pathELength_comp_le_of_tangentNorm_le_on_Icc S.metric
    (C := 2) (by norm_num) hγ (fun t ht => hf (γ t) (hmap ht))
    (fun t ht => hk.2 (γ t) (subset_closure (hmap ht)))
  have hbound : S.metric.edist (f L.base) (f x) < ENNReal.ofReal (2 * r) := by
    apply (hdist.trans hlength).trans_lt
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact ENNReal.mul_lt_mul_right (by norm_num : ENNReal.ofReal (2 : ℝ) ≠ 0)
      ENNReal.ofReal_ne_top hlen
  dsimp only [f] at hbound
  rw [G.unscaledOriginalEmbedding_base] at hbound
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound.le).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

theorem normalizedPotentialPullback_eventually_value_differential_bounded
    (hD : S.connection.CurvatureTensorCalculus) (p : M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop)
    (hcomplete : L.limitCarrier.metricComplete (L.limitFlow.metric 0))
    (K : Set L.limitCarrier.carrier) (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop, ∀ x ∈ K,
      |G.normalizedPotentialPullback L k x| ≤ B ∧
        ∀ v : TangentSpace (𝓡 3) x,
          |mvfderiv (𝓡 3) (G.normalizedPotentialPullback L k) x v| ≤
            B * (L.limitFlow.metric 0).tangentNorm x v := by
  obtain ⟨R, hR, hdist⟩ :=
    G.unscaledOriginalEmbedding_eventually_bounded_distance L hcomplete K hK
  obtain ⟨B, hB, hsource⟩ := S.exists_normalizedPotential_value_gradient_ball_bound hD R hR.le
  have hscale := G.normalizedPotentialPullback_scale_tendsto_atTop L hD p hescape
  refine ⟨2 * B, by positivity, ?_⟩
  filter_upwards [hdist, hscale.eventually_ge_atTop 1,
    G.unscaledOriginalEmbedding_tangentNorm_eventually_le L K hK] with k hk hks hkn x hx
  have hbounds := hsource (q (L.subsequence k)) hks
    (G.unscaledOriginalEmbedding L k x) (hk x hx)
  refine ⟨hbounds.1.trans (by linarith), fun v => ?_⟩
  have hchain : mvfderiv (𝓡 3) (G.normalizedPotentialPullback L k) x v =
      mvfderiv (𝓡 3) (S.normalizedPotential (q (L.subsequence k)))
        (G.unscaledOriginalEmbedding L k x)
        (mfderiv (𝓡 3) (𝓡 3) (G.unscaledOriginalEmbedding L k) x v) :=
    mvfderiv_comp_apply x
      (((S.normalizedPotential_contMDiff _).mdifferentiable (by simp)) _)
      (((G.unscaledOriginalEmbedding_contMDiffOn L k).contMDiffAt
        ((L.exhaustion_open k).mem_nhds (hkn.1 hx))).mdifferentiableAt (by simp)) v
  rw [hchain]
  exact (S.connection.abs_mvfderiv_le_gradient_norm _ _ _).trans
    ((mul_le_mul hbounds.2 (hkn.2 x hx v) (Real.sqrt_nonneg _) hB).trans_eq (by ring))

theorem normalizedPotentialPullback_eventually_value_gradient_bounded
    (hD : S.connection.CurvatureTensorCalculus) (p : M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop)
    (hcomplete : L.limitCarrier.metricComplete (L.limitFlow.metric 0))
    (K : Set L.limitCarrier.carrier) (hK : IsCompact K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop, ∀ x ∈ K,
      |G.normalizedPotentialPullback L k x| ≤ B ∧
        (L.limitFlow.metric 0).tangentNorm x
          ((L.limitFlow.connection 0).gradient (G.normalizedPotentialPullback L k) x) ≤ B := by
  obtain ⟨B, hB, hbound⟩ :=
    G.normalizedPotentialPullback_eventually_value_differential_bounded L hD p hescape hcomplete K hK
  refine ⟨B, hB, ?_⟩
  filter_upwards [hbound] with k hk x hx
  exact ⟨(hk x hx).1, ((L.limitFlow.connection 0).gradient_norm_le_iff _ _ hB).2 (hk x hx).2⟩

theorem normalizedPotentialPullback_eventually_coordinate_C1_bounded
    (hD : S.connection.CurvatureTensorCalculus) (p : M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop)
    (hcomplete : L.limitCarrier.metricComplete (L.limitFlow.metric 0))
    (z : L.limitCarrier.carrier) (K : Set (EuclideanSpace ℝ (Fin 3)))
    (hK : IsCompact K) (hKt : K ⊆ (extChartAt (𝓡 3) z).target) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k in atTop, ∀ x ∈ K,
      ‖(G.normalizedPotentialPullback L k ∘ (extChartAt (𝓡 3) z).symm) x‖ ≤ B ∧
        ‖fderiv ℝ (G.normalizedPotentialPullback L k ∘ (extChartAt (𝓡 3) z).symm) x‖ ≤ B := by
  let c := extChartAt (𝓡 3) z
  let g := L.limitFlow.metric 0
  let : NormedAddCommGroup (EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  have hc (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ c.target) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm x :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) z hx).contMDiffAt
      (extChartAt_target_mem_nhds' hx)
  have hcompact : IsCompact (c.symm '' K) :=
    hK.image_of_continuousOn ((contMDiffOn_extChartAt_symm (n := ∞) z).continuousOn.mono hKt)
  obtain ⟨A, hA, hbound⟩ := G.normalizedPotentialPullback_eventually_value_differential_bounded
    L hD p hescape hcomplete (c.symm '' K) hcompact
  have hcoeff : ContinuousOn (g.pullbackCoefficients c.symm) K := by
    intro x hx
    exact (g.contDiffAt_pullbackCoefficients (hc x (hKt hx))).continuousAt.continuousWithinAt
  obtain ⟨b, hb⟩ := hK.exists_bound_of_continuousOn hcoeff
  let C := |b| + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hchart (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ K) (v : EuclideanSpace ℝ (Fin 3)) :
      g.tangentNorm (c.symm x) (mfderiv (𝓡 3) (𝓡 3) c.symm x v) ≤ Real.sqrt C * ‖v‖ := by
    have hupper : g.pullbackCoefficients c.symm x v v ≤ C * ‖v‖ ^ 2 := by
      calc
        _ ≤ |g.pullbackCoefficients c.symm x v v| := le_abs_self _
        _ ≤ ‖g.pullbackCoefficients c.symm x‖ * ‖v‖ * ‖v‖ := by
          simpa only [Real.norm_eq_abs] using (g.pullbackCoefficients c.symm x).le_opNorm₂ v v
        _ ≤ C * ‖v‖ ^ 2 := by
          have hcb : ‖g.pullbackCoefficients c.symm x‖ ≤ C :=
            (hb x hx).trans (by dsimp [C]; linarith [le_abs_self b])
          simpa only [pow_two, mul_assoc] using mul_le_mul_of_nonneg_right hcb
            (mul_nonneg (norm_nonneg v) (norm_nonneg v))
    change Real.sqrt (g.pullbackCoefficients c.symm x v v) ≤ _
    calc
      _ ≤ Real.sqrt (C * ‖v‖ ^ 2) := Real.sqrt_le_sqrt hupper
      _ = Real.sqrt C * ‖v‖ := by rw [Real.sqrt_mul hC, Real.sqrt_sq (norm_nonneg v)]
  refine ⟨max A (A * Real.sqrt C), le_max_of_le_left hA, ?_⟩
  filter_upwards [hbound,
    G.unscaledOriginalEmbedding_tangentNorm_eventually_le L (c.symm '' K) hcompact]
    with k hk hkdom x hx
  have hximage : c.symm x ∈ c.symm '' K := mem_image_of_mem _ hx
  refine ⟨?_, le_trans ?_ (le_max_right _ _)⟩
  · simpa only [Real.norm_eq_abs, Function.comp_apply] using
      ((hk _ hximage).1.trans (le_max_left A (A * Real.sqrt C)))
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hA (Real.sqrt_nonneg _))
  intro v
  have hchain := mvfderiv_comp_apply x
    (((G.normalizedPotentialPullback_contMDiffOn L k).contMDiffAt
      ((L.exhaustion_open k).mem_nhds (hkdom.1 hximage))).mdifferentiableAt (by simp))
    ((hc x (hKt hx)).mdifferentiableAt (by simp)) v
  simp only [mvfderiv, ContinuousLinearMap.comp_apply, mfderiv_eq_fderiv] at hchain
  change fderiv ℝ (G.normalizedPotentialPullback L k ∘ c.symm) x v = _ at hchain
  rw [Real.norm_eq_abs, hchain]
  exact ((hk _ hximage).2 _).trans
    ((mul_le_mul_of_nonneg_left (hchart x hx v) hA).trans_eq (by ring))

end PoincareConjecture.ShrinkingSolitonFlow
