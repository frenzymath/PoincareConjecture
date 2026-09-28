import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.ZeroRatio.Backward.FilledDomainDecay

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.RicciFlow

theorem eventually_past_ball_curvature_lt_of_later_scalar_tendsto_zero
    {n : ℕ} {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, T3Space (M i)]
    [∀ i, SecondCountableTopology (M i)] [∀ i, ConnectedSpace (M i)]
    [∀ i, NoncompactSpace (M i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M i)]
    [∀ i, IsManifold (𝓡 n) ∞ (M i)]
    (hC : RicciFlowCurvatureTheory.{u}) (F : ∀ i, RicciFlow n (M i) (Iic 0))
    (hcomplete : ∀ i t, t ≤ 0 → MetricComplete ((F i).metric t))
    (hoperator : ∀ i t, t ≤ 0 → ∀ x, ((F i).connection t).NonnegativeCurvatureOperator x)
    (hbounded : ∀ i, ∃ K : ℝ, 0 ≤ K ∧
      ∀ t ≤ 0, ∀ x, ((F i).connection t).curvatureTensorNorm x ≤ K)
    {a b : ℝ} (hab : a < b) (hb : b ≤ 0)
    (y : ∀ i, M i)
    (hscalar : Tendsto (fun i => ((F i).connection b).scalarCurvature (y i)) atTop (𝓝 0))
    (r : ℝ) (hr : 0 < r) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
      ∀ s ≤ a, ∀ x ∈ ((F i).metric a).ball (y i) r,
        ((F i).connection s).curvatureTensorNorm x < ε := by
  let B := fun i => ((F i).metric a).ball (y i) r
  have hdistance : ∀ᶠ i in atTop, ∀ x ∈ B i,
      (((F i).metric a).edist x (y i)).toReal ≤ r := by
    apply Eventually.of_forall
    intro i x hx
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M i → Type _) :=
      ⟨((F i).metric a).toRiemannianMetric⟩
    have hcomm : ((F i).metric a).edist x (y i) =
        ((F i).metric a).edist (y i) x := Manifold.riemannianEDist_comm
    rw [hcomm]
    exact (ENNReal.toReal_lt_of_lt_ofReal hx).le
  have hterminal := eventually_curvatureTensorNorm_lt_on_of_later_scalar_tendsto_zero
    hC F hcomplete hoperator hbounded hab hb y B hscalar hdistance
  intro ε hε
  let C : ℝ := (n : ℝ) ^ 2 * (n : ℝ) ^ 2
  have hCnonneg : 0 ≤ C := by dsimp [C]; positivity
  let δ : ℝ := ε / (C + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hscale : (n : ℝ) ^ 2 * ((n : ℝ) ^ 2 * δ) < ε := by
    calc
      (n : ℝ) ^ 2 * ((n : ℝ) ^ 2 * δ) = C * ε / (C + 1) := by
        dsimp [C, δ]
        ring
      _ < ε := (div_lt_iff₀ (by positivity : 0 < C + 1)).mpr (by nlinarith)
  filter_upwards [hterminal δ hδ] with i hi
  obtain ⟨K, hK, hbound⟩ := hbounded i
  have hscal : ∀ x ∈ B i, ((F i).connection a).scalarCurvature x ≤ (n : ℝ) ^ 2 * δ := by
    intro x hx
    exact (le_abs_self _).trans
      ((((F i).connection a).abs_scalarCurvature_le_curvatureTensorNorm x).trans
        (mul_le_mul_of_nonneg_left (hi x hx).le (sq_nonneg _)))
  intro s hs x hx
  exact ((F i).curvatureTensorNorm_le_of_bounded_ancient_terminal_scalar
    hC (hcomplete i) (hoperator i) hK hbound (hab.le.trans hb) hscal s hs x hx).trans_lt
      hscale

theorem eventually_ball_volume_lower_bound_of_later_scalar_tendsto_zero
    {n : ℕ} {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, T3Space (M i)]
    [∀ i, SecondCountableTopology (M i)] [∀ i, ConnectedSpace (M i)]
    [∀ i, NoncompactSpace (M i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M i)]
    [∀ i, IsManifold (𝓡 n) ∞ (M i)]
    [∀ i, MeasurableSpace (M i)] [∀ i, BorelSpace (M i)]
    (hC : RicciFlowCurvatureTheory.{u}) (F : ∀ i, RicciFlow n (M i) (Iic 0))
    (hcomplete : ∀ i t, t ≤ 0 → MetricComplete ((F i).metric t))
    (hoperator : ∀ i t, t ≤ 0 → ∀ x, ((F i).connection t).NonnegativeCurvatureOperator x)
    (hbounded : ∀ i, ∃ K : ℝ, 0 ≤ K ∧
      ∀ t ≤ 0, ∀ x, ((F i).connection t).curvatureTensorNorm x ≤ K)
    {κ : ℝ}
    (hnoncollapse : ∀ i t, t ≤ 0 → ∀ x : M i, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Icc (t - r ^ 2) t, ∀ z ∈ ((F i).metric t).ball x r,
        ((F i).connection s).curvatureTensorNorm z ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤
        ((F i).metric t).volumeMeasure (((F i).metric t).ball x r))
    {a b : ℝ} (hab : a < b) (hb : b ≤ 0)
    (y : ∀ i, M i)
    (hscalar : Tendsto (fun i => ((F i).connection b).scalarCurvature (y i)) atTop (𝓝 0))
    (r : ℝ) (hr : 0 < r) :
    ∀ᶠ i in atTop, ENNReal.ofReal (κ * r ^ n) ≤
      ((F i).metric a).volumeMeasure (((F i).metric a).ball (y i) r) := by
  filter_upwards [eventually_past_ball_curvature_lt_of_later_scalar_tendsto_zero
    hC F hcomplete hoperator hbounded hab hb y hscalar r hr (r⁻¹ ^ 2) (by positivity)]
    with i hi
  apply hnoncollapse i a (hab.le.trans hb) (y i) r hr
  intro s hs x hx
  exact (hi s hs.2 x hx).le

end PoincareConjecture.RicciFlow
