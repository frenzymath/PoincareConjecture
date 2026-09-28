import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Completeness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space

namespace RicciFlow

theorem metricComplete_terminal_of_local_curvature_bound
    {n : ℕ} (C : FlowCarrier n) (F : RicciFlow n C.carrier (Iic 0)) (p : C.carrier)
    {τ : ℝ} (hτ : τ ≤ 0) (hcomplete : C.metricComplete (F.metric τ))
    (hcurv : ∀ A : ℝ, 0 < A → ∃ K : ℝ, 0 ≤ K ∧
      ∀ t ∈ Icc τ 0, ∀ x ∈ (F.metric 0).ball p A,
        (F.connection t).curvatureTensorNorm x ≤ K) :
    C.metricComplete (F.metric 0) := by
  let d₀ := (C.metricEMetricSpace (F.metric τ)).toPseudoEMetricSpace
  let d₁ := (C.metricEMetricSpace (F.metric 0)).toPseudoEMetricSpace
  change @CompleteSpace C.carrier d₁.toUniformSpace
  apply Poincare.completeSpace_of_continuous_local_edist_bound d₀ d₁ p hcomplete
  · change @Continuous C.carrier C.carrier C.topologicalSpace C.topologicalSpace id
    exact continuous_id
  · exact fun x => @Poincare.edist_ne_top_of_preconnected C.carrier d₁
      (C.preconnected_metricEMetricSpace (F.metric 0)) x p
  · intro R
    let r : ℝ := R + 1
    have hr : 0 < r := by dsimp only [r]; positivity
    obtain ⟨K, _, hK⟩ := hcurv (3 * r) (by positivity)
    let L : ℝ := (n : ℝ) ^ 3 * K
    let A : ℝ := Real.exp (L * |τ|)
    refine ⟨Real.toNNReal A, fun x y hx hy => ?_⟩
    have hRic : ∀ t ∈ Icc τ 0, ∀ z ∈ (F.metric 0).ball p (3 * r),
        ∀ v : C.tangent z,
          |(F.connection t).ricci z v v| ≤ L * (F.metric t).inner z v v := by
      intro t ht z hz v
      have hQ : 0 ≤ (F.metric t).inner z v v := by
        by_cases hv : v = 0
        · subst v; simp
        · exact ((F.metric t).pos z v hv).le
      have hnorm := (F.connection t).abs_ricci_quadratic_le_curvatureTensorNorm z v
      have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) z) = n := finrank_euclideanSpace_fin
      simp only [Fintype.card_fin, hdim] at hnorm
      exact hnorm.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hK t ht z hz) (by positivity)) hQ)
    have hR : (R : ℝ≥0∞) < ENNReal.ofReal r := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_lt_ofReal_iff hr |>.mpr (by dsimp only [r]; linarith)
    have hmem (z : C.carrier) (hz : d₁.edist z p ≤ R) : z ∈ (F.metric 0).ball p r := by
      change d₁.edist p z < ENNReal.ofReal r
      rw [d₁.edist_comm]
      exact hz.trans_lt hR
    have hdist := F.edist_le_exp_mul_of_ricci_bound (convex_Icc τ 0)
      (fun _ ht => ht.2) p r L hr
      (show (0 : ℝ) ∈ Icc τ 0 from ⟨hτ, le_rfl⟩)
      (show τ ∈ Icc τ 0 from ⟨le_rfl, hτ⟩) hRic (hmem x hx) (hmem y hy)
    change (F.metric τ).edist x y ≤ ENNReal.ofReal A * (F.metric 0).edist x y
    simpa only [sub_zero] using hdist

end RicciFlow

namespace AncientCompactness

theorem eventually_mem_source_ball_of_compact_pullback_bound
    {n : ℕ} (L : FlowCarrier.{0} n) (C : ℕ → FlowCarrier.{0} n)
    (g : L.metric) (h : ∀ k, (C k).metric) (q : L.carrier) (p : ∀ k, (C k).carrier)
    (e : ∀ k, L.carrier → (C k).carrier)
    (hbase : ∀ᶠ k in atTop, e k q = p k)
    (hsmooth : ∀ A : Set L.carrier, IsCompact A → ∀ᶠ k in atTop,
      ∀ x ∈ A, ContMDiffAt (𝓡 n) (𝓡 n) 1 (e k) x)
    (hbound : ∀ A : Set L.carrier, IsCompact A → ∀ᶠ k in atTop,
      ∀ x ∈ A, ∀ v : L.tangent x,
        (h k).tangentNorm (e k x) (mfderiv (𝓡 n) (𝓡 n) (e k) x v) ≤
          2 * g.tangentNorm x v)
    {r : ℝ} {x : L.carrier} (hx : x ∈ g.ball q r) :
    ∀ᶠ k in atTop, e k x ∈ (h k).ball (p k) (2 * r) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : L.carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : ∀ z : L.carrier, ENormSMulClass ℝ (TangentSpace (𝓡 n) z) :=
    fun _ => inferInstance
  change Manifold.riemannianEDist (𝓡 n) q x < ENNReal.ofReal r at hx
  obtain ⟨γ, hγ0, hγ1, hγ, hlength, _⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hx
      (zero_lt_one : (0 : ℝ) < 1)
  have hA : IsCompact (γ '' Icc (0 : ℝ) 1) := isCompact_Icc.image hγ.continuous
  filter_upwards [hbase, hsmooth _ hA, hbound _ hA] with k hk hs hb
  let η : ℝ → (C k).carrier := fun t => e k (γ t)
  have hη : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 η (Icc 0 1) := by
    intro t ht
    exact ((hs _ (mem_image_of_mem γ ht)).comp t hγ.contMDiffAt).contMDiffWithinAt
  have hlen : (h k).pathELength η 0 1 ≤ ENNReal.ofReal 2 * g.pathELength γ 0 1 := by
    rw [RiemannianMetric.pathELength_eq_lintegral_tangentNorm,
      RiemannianMetric.pathELength_eq_lintegral_tangentNorm,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' measurableSet_Icc
    intro t ht
    have hchain : mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) η t 1 =
        mfderiv (𝓡 n) (𝓡 n) (e k) (γ t)
          (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) γ t 1) :=
      mfderiv_comp_apply t ((hs _ (mem_image_of_mem γ ht)).mdifferentiableAt (by simp))
        (hγ.mdifferentiable (by simp) t) (1 : ℝ)
    rw [hchain]
    exact (ENNReal.ofReal_le_ofReal (hb _ (mem_image_of_mem γ ht) _)).trans_eq
      (ENNReal.ofReal_mul (by norm_num))
  have hdist : (h k).edist (p k) (e k x) ≤ (h k).pathELength η 0 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : (C k).carrier → Type _) :=
      ⟨(h k).toRiemannianMetric⟩
    exact Manifold.riemannianEDist_le_pathELength hη
      (by simpa only [η, hγ0] using hk) (by simp only [η, hγ1]) zero_le_one
  change (h k).edist (p k) (e k x) < ENNReal.ofReal (2 * r)
  calc
    _ ≤ ENNReal.ofReal 2 * g.pathELength γ 0 1 := hdist.trans hlen
    _ < ENNReal.ofReal 2 * ENNReal.ofReal r :=
      (ENNReal.mul_lt_mul_right (by norm_num : ENNReal.ofReal (2 : ℝ) ≠ 0)
        ENNReal.ofReal_ne_top) hlength
    _ = ENNReal.ofReal (2 * r) := (ENNReal.ofReal_mul (by norm_num)).symm

end AncientCompactness

namespace AncientKappaSequence

attribute [local instance] FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t3Space FlowCarrier.secondCountable

local instance terminalCompleteCarrierConnected (D : FlowCarrier 3) : ConnectedSpace D.carrier :=
  connectedSpace_iff_univ.mpr D.connected

theorem terminal_curvature_bound_of_source_convergence
    (C : ℕ → FlowCarrier.{0} 3) (K : ∀ k, AncientKappaSolution 3 (C k).carrier)
    (p : ∀ k, (C k).carrier)
    (L : FlowCarrier.{0} 3) (F : RicciFlow 3 L.carrier (Iic 0)) (q : L.carrier)
    (σ : ℕ → ℕ) (e : ∀ k, L.carrier → (C (σ k)).carrier)
    (hsource : ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 ≤ B ∧
      ∀ k t, t ≤ 0 → ∀ x ∈ ((K k).flow.metric 0).ball (p k) A,
        |((K k).flow.connection t).curvatureTensorNorm x| ≤ B)
    (hball : ∀ A : ℝ, 0 < A → ∀ x ∈ (F.metric 0).ball q A,
      ∀ᶠ k in atTop, e k x ∈ ((K (σ k)).flow.metric 0).ball (p (σ k)) (2 * A))
    (hconverges : ∀ t : ℝ, t ≤ 0 → ∀ x : L.carrier,
      Tendsto (fun k => ((K (σ k)).flow.connection t).curvatureTensorNorm (e k x))
        atTop (𝓝 ((F.connection t).curvatureTensorNorm x))) :
    ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 ≤ B ∧
      ∀ t : ℝ, t ≤ 0 → ∀ x ∈ (F.metric 0).ball q A,
        (F.connection t).curvatureTensorNorm x ≤ B := by
  intro A hA
  obtain ⟨B, hB, hbound⟩ := hsource (2 * A) (by positivity)
  refine ⟨B, hB, fun t ht x hx => ?_⟩
  apply le_of_tendsto (hconverges t ht x)
  filter_upwards [hball A hA x hx] with k hk
  exact (le_abs_self _).trans (hbound (σ k) t ht (e k x) hk)

end AncientKappaSequence
end PoincareConjecture
