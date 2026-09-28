import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.AnnularPotential
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.TerminalMetric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.AnnularVariation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.AnnularRigidity

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric TopologicalSpace
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.RicciFlow

set_option maxHeartbeats 800000 in

theorem false_of_positive_finite_scalar_ratio_and_corresponding_side_comparison
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [MeasurableSpace M] [BorelSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ} (hκ : 0 < κ)
    (hnoncollapse : ∀ t ≤ 0, ∀ x : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ y ∈ (F.metric t).ball x r,
        (F.connection s).curvatureTensorNorm y ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤ (F.metric t).volumeMeasure ((F.metric t).ball x r))
    (hn : 1 ≤ n) (t₀ : ℝ) (ht₀ : t₀ ≤ 0) (p : M) (q : ℕ → M)
    (hQ : ∀ i, 0 < (F.connection t₀).scalarCurvature (q i))
    (hd : Tendsto (fun i => ((F.metric t₀).edist p (q i)).toReal) atTop atTop)
    {A C L : ℝ} (hA : 0 < A) (hCnonneg : 0 ≤ C)
    (hratio : Tendsto (fun i => (F.connection t₀).scalarCurvature (q i) *
      ((F.metric t₀).edist p (q i)).toReal ^ 2) atTop (𝓝 A))
    (hdecay : ∀ x, L ≤ ((F.metric t₀).edist p x).toReal →
      (F.connection t₀).scalarCurvature x * ((F.metric t₀).edist p x).toReal ^ 2 ≤ C)
    (hcomparison : ∀ a b : ℝ, 0 < a → 0 < b → ∀ α β : ℝ → M,
      α 0 = p → β 0 = p →
      (∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) a,
        (F.metric t₀).edist (α s) (α t) = ENNReal.ofReal |s - t|) →
      (∀ s ∈ Icc (0 : ℝ) b, ∀ t ∈ Icc (0 : ℝ) b,
        (F.metric t₀).edist (β s) (β t) = ENNReal.ofReal |s - t|) →
      ∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) b,
        s ^ 2 + t ^ 2 - 2 * s * t *
          ((a ^ 2 + b ^ 2 - ((F.metric t₀).edist (α a) (β b)).toReal ^ 2) / (2 * a * b)) ≤
            ((F.metric t₀).edist (α s) (β t)).toReal ^ 2) : False := by
  obtain ⟨K₀, S, ρ, _hK₀, hS, hρ, hρS, σ, hσ, _L₀, Φ,
    _hcompleteG, _hoperatorG, _hcurvG, _hscalarG, hcharts,
    B, hB, hjets, U, hzeroU, hU, Flimit, hFcoeff, _hFlower,
    hFoperator, hFscalar, _hFnorm, _hFscalarLimit⟩ :=
    F.exists_normalized_annular_ancient_flow hC hcomplete hoperator hK hbound hκ
      hnoncollapse hn t₀ ht₀ p q hQ hd hA hCnonneg hratio hdecay
  let G := fun k => F.ancientRescaleAt
    ((F.connection t₀).scalarCurvature (q (σ k))) (hQ (σ k)) t₀ ht₀
  obtain ⟨τ, hτ, C₀, f, hLip, hpotential, _hfzero, hfzeroPos, _hfnonneg, hjetsτ⟩ :=
    F.exists_radial_square_potential_of_normalized_annular_limit t₀ ht₀ p q hQ hA hratio
      σ hσ hρ (by linarith : ρ ≤ S) Φ
      (fun k => (hcharts k).1) (fun k => (hcharts k).2.2.1) B hB
      (fun k => (hcharts k).2.2.2.2.2.2) hjets
  obtain ⟨gLimit, _DLimit, V, hzeroV, hVU, _hVcoeff, hmetric, hcoeffLimit⟩ :=
    exists_terminal_metric_of_ancient_chart_limit (fun k => G (τ k))
      (fun k => Φ (τ k)) U hzeroU hU Flimit B hB
      (fun x v w => hFcoeff 0 (by simp) x v w) hjetsτ
  let Vsmall : Opens (EuclideanSpace ℝ (Fin n)) :=
    V ⊓ ⟨Metric.ball 0 (ρ / 2), isOpen_ball⟩
  have hzeroVsmall : (0 : EuclideanSpace ℝ (Fin n)) ∈ Vsmall :=
    ⟨hzeroV, Metric.mem_ball_self (by positivity)⟩
  have hVsmallV : Vsmall ≤ V := inf_le_left
  have hVsmallBall : (Vsmall : Set (EuclideanSpace ℝ (Fin n))) ⊆ Metric.ball 0 (ρ / 2) :=
    fun _ hx => hx.2
  let Q : ℕ → ℝ := fun k => (F.connection t₀).scalarCurvature (q (σ (τ k)))
  have hQ' (k : ℕ) : 0 < Q k := hQ _
  have hmetricG (k : ℕ) : (G (τ k)).metric 0 = rescaledMetric (F.metric t₀) (Q k) (hQ' k) := by
    simp only [G, ancientRescaleAt_metric, zero_div, add_zero, Q]
  have hQzero : Tendsto (fun k => Real.sqrt (Q k)) atTop (𝓝 0) := by
    have hz := (F.scalarCurvature_tendsto_zero_of_finite_ratio t₀ p q hd hratio).sqrt
    simpa only [Real.sqrt_zero, Function.comp_def, Q] using
      hz.comp (hσ.comp hτ).tendsto_atTop
  obtain ⟨W, hWo, hzeroW, hWVsmall, _hfposW, hidentity⟩ :=
    (F.metric t₀).exists_local_minimizing_identity_of_rescaled_normal_charts
      (hcomplete t₀ ht₀) p hcomparison gLimit (fun k => q (σ (τ k))) Q hQ' hQzero
      (fun k => Φ (τ k)) hS (fun k => (hcharts (τ k)).1)
      (fun k => by rw [← hmetricG]; exact (hcharts (τ k)).2.1)
      (fun k x hx => by rw [← hmetricG]; exact (hcharts (τ k)).2.2.2.2.2.2 x hx)
      Vsmall.isOpen hzeroVsmall
      (fun E hE hEV => by
        simpa only [← hmetricG] using hcoeffLimit E hE (hEV.trans hVsmallV))
      f hfzeroPos (by
        simpa only [← hmetricG] using hpotential.mono
          (hVsmallBall.trans ball_subset_closedBall))
  let Wopen : Opens (EuclideanSpace ℝ (Fin n)) := ⟨W, hWo⟩
  have hWVU : Wopen ≤ U := fun x hx => hVU (hVsmallV (hWVsmall hx))
  apply Flimit.false_of_scalar_one_annular_minimizing_identity hC hFoperator gLimit Wopen
    hWVU (fun x hx v w => hmetric x (hVsmallV (hWVsmall hx)) v w) f
    (hWVsmall.trans hVsmallBall) hLip _ ⟨0, hzeroU⟩ hzeroW hFscalar
  intro γ ε hε hγ hγW hmin t ht
  apply hidentity (γ 0) (hγW (by simp)) (γ t) (hγW ht) (γ 1) (hγW (by simp)) t ht
  · rw [hmin 0 (by simp) t ht, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
      zero_sub, abs_neg, abs_of_nonneg ht.1]
  · rw [hmin t ht 1 (by simp), ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
      abs_of_nonpos (sub_nonpos.mpr ht.2)]
    ring

end PoincareConjecture.RicciFlow
