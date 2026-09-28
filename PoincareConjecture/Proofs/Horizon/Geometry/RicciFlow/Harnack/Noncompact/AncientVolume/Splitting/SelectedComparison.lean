import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.SelectedEndpoints
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.SmallSelectedLine
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.SectionalBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Polar.NoBranching











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal

universe u

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [T3Space M] [ConnectedSpace M] in
private theorem initial_velocity_eq_of_chart_deriv
    {g : RiemannianMetric n M} {γ : ℝ → M} {I : Set ℝ}
    (hγ : g.IsGeodesicOn γ I) (h0 : (0 : ℝ) ∈ I)
    {p : M} (hp : γ 0 = p) {v : EuclideanSpace ℝ (Fin n)}
    (hd : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1 = v := by
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) (γ 0) := by
    rw [hp]
    exact mdifferentiableAt_extChartAt (mem_chart_source _ p)
  have hchain := mfderiv_comp 0 hc ((hγ.contMDiffAt h0).mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at hchain
  have hv := congrArg (fun L => L (1 : ℝ)) hchain
  change (fderiv ℝ (fun t => extChartAt (𝓡 n) p (γ t)) 0) 1 =
    mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) (γ 0)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ 0 1) at hv
  rw [fderiv_eq_smul_deriv, one_smul, hd.deriv] at hv
  have hid : ∀ w : TangentSpace (𝓡 n) (γ 0),
      mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) p) (γ 0) w = w := by
    rw [hp]
    intro w
    rw [mfderiv_extChartAt_self]
    rfl
  exact (hv.trans (hid _)).symm

private theorem unit_reparameterization_of_fractional_segment
    (g : RiemannianMetric n M) {p q : M} {ε : ℝ} {γ : ℝ → M}
    (hε : 0 < ε) (hγ : g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)))
    (hγ0 : γ 0 = p) (hγ1 : γ 1 = q)
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist p q)
    {v : TangentSpace (𝓡 n) p}
    (hd : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t))
      ((g.edist p q).toReal • v) 0)
    (ha : 0 < (g.edist p q).toReal) :
    let a := (g.edist p q).toReal
    let η := fun t => γ (a⁻¹ * t)
    g.IsGeodesicOn η (Icc 0 a) ∧ η 0 = p ∧ η a = q ∧
      mfderiv 𝓘(ℝ, ℝ) (𝓡 n) η 0 1 = v ∧
      (∀ t ∈ Icc 0 a, g.tangentNorm (η t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) η t 1) = 1) ∧
      ∀ s ∈ Icc 0 a, ∀ t ∈ Icc 0 a,
        g.edist (η s) (η t) = ENNReal.ofReal |s - t| := by
  let a := (g.edist p q).toReal
  let η := fun t => γ (a⁻¹ * t)
  have ha' : 0 < a := ha
  have hparam {t : ℝ} (ht : t ∈ Icc 0 a) : a⁻¹ * t ∈ Icc (0 : ℝ) 1 := by
    rw [mul_comm, ← div_eq_mul_inv]
    exact ⟨div_nonneg ht.1 ha.le, (div_le_one ha).mpr ht.2⟩
  have hgeo : g.IsGeodesicOn η (Icc 0 a) := by
    intro t ht
    apply hγ.comp_mul a⁻¹ t
    have ht' := hparam ht
    exact ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
  have hzero : η 0 = p := by simpa only [η, mul_zero] using hγ0
  have hend : η a = q := by simpa only [η, inv_mul_cancel₀ ha'.ne'] using hγ1
  have hderiv : HasDerivAt (fun t => extChartAt (𝓡 n) p (η t)) v 0 := by
    have hd0 : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) (a • v) (a⁻¹ * 0) := by
      simpa only [mul_zero] using hd
    have h := hd0.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_mul a⁻¹)
    simpa only [Function.comp_def, mul_one, smul_smul, inv_mul_cancel₀ ha'.ne', one_smul]
      using h
  have hvel := initial_velocity_eq_of_chart_deriv hgeo ⟨le_rfl, ha.le⟩ hzero hderiv
  have hnorm : g.tangentNorm p v = 1 := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
    have h := congrArg ENNReal.toReal
      (hγ.initial_tangentNorm_eq_of_edist_segment hε hγ0 hd hmin)
    change (ENNReal.ofReal ‖a • v‖).toReal = a at h
    rw [ENNReal.toReal_ofReal (norm_nonneg _), norm_smul, Real.norm_eq_abs, abs_of_pos ha'] at h
    exact (mul_left_cancel₀ ha'.ne' (h.trans (mul_one a).symm))
  refine ⟨hgeo, hzero, hend, hvel, ?_, ?_⟩
  · intro t ht
    rw [Poincare.VolumeComparison.tangentNorm_eq_of_mem_Icc g hgeo ht
      ⟨le_rfl, ha.le⟩, hvel]
    dsimp only [η]
    rw [mul_zero, hγ0]
    exact hnorm
  · intro s hs t ht
    change g.edist (γ (a⁻¹ * s)) (γ (a⁻¹ * t)) = _
    rw [hmin _ (hparam hs) _ (hparam ht),
      ← ENNReal.ofReal_toReal (g.edist_ne_top p q),
      ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    rw [show a⁻¹ * s - a⁻¹ * t = a⁻¹ * (s - t) by ring,
      abs_mul, abs_of_pos (inv_pos.mpr ha)]
    change a⁻¹ * |s - t| * a = |s - t|
    rw [mul_right_comm, inv_mul_cancel₀ ha'.ne', one_mul]



theorem toponogov_hinge_of_fractional_segments
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (p x y : M) (ε₁ ε₂ : ℝ) (γ₁ γ₂ : ℝ → M)
    (v w : TangentSpace (𝓡 n) p) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    (hγ₁ : g.IsGeodesicOn γ₁ (Ioo (-ε₁) (1 + ε₁)))
    (hγ₂ : g.IsGeodesicOn γ₂ (Ioo (-ε₂) (1 + ε₂)))
    (hγ₁0 : γ₁ 0 = p) (hγ₁1 : γ₁ 1 = x) (hγ₂0 : γ₂ 0 = p) (hγ₂1 : γ₂ 1 = y)
    (hmin₁ : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      g.edist (γ₁ a) (γ₁ b) = ENNReal.ofReal |a - b| * g.edist p x)
    (hmin₂ : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      g.edist (γ₂ a) (γ₂ b) = ENNReal.ofReal |a - b| * g.edist p y)
    (hd₁ : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ₁ t)) ((g.edist p x).toReal • v) 0)
    (hd₂ : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ₂ t)) ((g.edist p y).toReal • w) 0) :
    (g.edist x y).toReal ^ 2 ≤ (g.edist p x).toReal ^ 2 + (g.edist p y).toReal ^ 2 -
      2 * (g.edist p x).toReal * (g.edist p y).toReal * g.inner p v w := by
  have hcomm (x y : M) : (g.edist x y).toReal = (g.edist y x).toReal := by
    let := g.toMetricSpace
    exact dist_comm x y
  by_cases hxp : x = p
  · rw [hxp]
    simp [RiemannianMetric.edist, Manifold.riemannianEDist_self]
  by_cases hyp : y = p
  · rw [hyp, hcomm x p]
    simp [RiemannianMetric.edist, Manifold.riemannianEDist_self]
  have ha : 0 < (g.edist p x).toReal := by
    let := g.toMetricSpace
    exact dist_pos.mpr (Ne.symm hxp)
  have hb : 0 < (g.edist p y).toReal := by
    let := g.toMetricSpace
    exact dist_pos.mpr (Ne.symm hyp)
  obtain ⟨hη₁, hη₁0, hη₁a, hv, _, hη₁min⟩ :=
    unit_reparameterization_of_fractional_segment g hε₁ hγ₁ hγ₁0 hγ₁1 hmin₁ hd₁ ha
  obtain ⟨hη₂, hη₂0, hη₂b, hw, hη₂speed, hη₂min⟩ :=
    unit_reparameterization_of_fractional_segment g hε₂ hγ₂ hγ₂0 hγ₂1 hmin₂ hd₂ hb
  simpa only [hη₁a, hη₂b, hv, hw] using
    g.toponogov_hinge D hcomplete hsec ha hb hη₁ hη₂ hη₁0 hη₂0 hη₂speed hη₁min hη₂min

set_option maxHeartbeats 800000 in



theorem exists_selected_normalized_opposite_segments
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)
    (p : M) (q : ℕ → M) (r Q : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) (hQ : ∀ i, 0 < Q i)
    (hdtop : Tendsto (fun i => (g.edist p (q i)).toReal) atTop atTop)
    (hDtop : Tendsto (fun i => (g.edist p (q i)).toReal * Real.sqrt (Q i)) atTop atTop)
    (hLtop : Tendsto (fun i => r i * Real.sqrt (Q i)) atTop atTop)
    (hsmall : Tendsto (fun i => r i / (g.edist p (q i)).toReal) atTop (𝓝 0))
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      let G := fun i => rescaledMetric g (Q (σ i)) (hQ (σ i))
      ∃ s : ℕ → ℝ, ∃ minus plus : ℕ → ℝ → M,
        (∀ i, 0 < s i ∧ K * s i ≤ r (σ i) * Real.sqrt (Q (σ i))) ∧
        Tendsto (fun i => s i / (r (σ i) * Real.sqrt (Q (σ i)))) atTop (𝓝 0) ∧
        Tendsto (fun i => s i / 2) atTop atTop ∧
        (∀ i, minus i 0 = q (σ i) ∧ plus i 0 = q (σ i) ∧
          minus i (s i / 2) ∈ (G i).ball (q (σ i)) (s i) ∧
          plus i (s i / 2) ∈ (G i).ball (q (σ i)) (s i)) ∧
        (∀ i, ∀ a ∈ Icc (0 : ℝ) (s i / 2), ∀ b ∈ Icc (0 : ℝ) (s i / 2),
          ((G i).edist (minus i a) (minus i b)).toReal = |a - b|) ∧
        (∀ i, ∀ a ∈ Icc (0 : ℝ) (s i / 2), ∀ b ∈ Icc (0 : ℝ) (s i / 2),
          ((G i).edist (plus i a) (plus i b)).toReal = |a - b|) ∧
        Tendsto (fun i =>
          ((s i / 2) ^ 2 + (s i / 2) ^ 2 -
            ((G i).edist (minus i (s i / 2)) (plus i (s i / 2))).toReal ^ 2) /
              (2 * (s i / 2) * (s i / 2))) atTop (𝓝 (-1)) := by
  have hcomp : ∀ i j (minus plus : ℝ → M) (A B : ℝ), 0 < A → 0 < B →
      minus 0 = q i → minus A = p → plus 0 = q i → plus B = q j →
      (∀ s ∈ Icc (0 : ℝ) A, ∀ t ∈ Icc (0 : ℝ) A,
        ((rescaledMetric g (Q i) (hQ i)).edist (minus s) (minus t)).toReal = |s - t|) →
      (∀ s ∈ Icc (0 : ℝ) B, ∀ t ∈ Icc (0 : ℝ) B,
        ((rescaledMetric g (Q i) (hQ i)).edist (plus s) (plus t)).toReal = |s - t|) →
      ∀ s ∈ Icc (0 : ℝ) A, ∀ t ∈ Icc (0 : ℝ) B,
        s ^ 2 + t ^ 2 - 2 * s * t *
          ((A ^ 2 + B ^ 2 - ((rescaledMetric g (Q i) (hQ i)).edist p (q j)).toReal ^ 2) /
            (2 * A * B)) ≤
          ((rescaledMetric g (Q i) (hQ i)).edist (minus s) (plus t)).toReal ^ 2 := by
    intro i j minus plus A B hA hB hm0 hmA hp0 hpB hm hp
    let gi := rescaledMetric g (Q i) (hQ i)
    let Di := rescaledMetric_connection g D (Q i) (hQ i)
    have hseci : Di.NonnegativeSectionalCurvature := by
      intro x v w
      rw [rescaledMetric_curvatureTensor]
      exact mul_nonneg (hQ i).le (hsec x v w)
    have hm' : ∀ s ∈ Icc (0 : ℝ) A, ∀ t ∈ Icc (0 : ℝ) A,
        gi.edist (minus s) (minus t) = ENNReal.ofReal |s - t| := by
      intro s hs t ht
      rw [← ENNReal.ofReal_toReal (gi.edist_ne_top _ _), hm s hs t ht]
    have hp' : ∀ s ∈ Icc (0 : ℝ) B, ∀ t ∈ Icc (0 : ℝ) B,
        gi.edist (plus s) (plus t) = ENNReal.ofReal |s - t| := by
      intro s hs t ht
      rw [← ENNReal.ofReal_toReal (gi.edist_ne_top _ _), hp s hs t ht]
    simpa only [hmA, hpB] using gi.toponogov_corresponding_side_of_edist_segments
      Di (metricComplete_rescaledMetric g (Q i) (hQ i) hcomplete) hseci
      hA hB hm0 hp0 hm' hp'
  obtain ⟨σ, hσ, _, ε, γ, v, vlim, _, _, _, k, _, _,
      s, minus, plus, hs, hsmall', hstop, hbase, hminus, hplus, hangle⟩ :=
    g.exists_selected_normalized_opposite_segments_of_comparison hcomplete
      p q r Q hr hQ hdtop hDtop hLtop hsmall hK
      (g.toponogov_hinge_of_fractional_segments D hcomplete hsec p) hcomp
  exact ⟨σ, hσ, s, minus, plus, hs, hsmall', hstop, hbase, hminus, hplus, hangle⟩

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold
attribute [local instance] smallCarrier smallChartedSpace smallIsManifold

set_option maxHeartbeats 1000000 in




theorem exists_isometric_line_of_selected_small_rescalings
    {m : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M] [IsManifold (𝓡 (m + 1)) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m)
    (F : RicciFlow (m + 1) M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (t₀ : ℝ) (ht₀ : t₀ < 0) (p : M) (q : ℕ → M) (r Q : ℕ → ℝ)
    (hr : ∀ i, 0 < r i) (hQ : ∀ i, 0 < Q i)
    (hscalar : ∀ i, ∀ x ∈ (F.metric t₀).ball (q i) (r i),
      (F.connection t₀).scalarCurvature x ≤ 4 * Q i)
    (hdtop : Tendsto (fun i => ((F.metric t₀).edist p (q i)).toReal) atTop atTop)
    (hDtop : Tendsto (fun i => ((F.metric t₀).edist p (q i)).toReal * Real.sqrt (Q i))
      atTop atTop)
    (hLtop : Tendsto (fun i => r i * Real.sqrt (Q i)) atTop atTop)
    (hsmall : Tendsto (fun i => r i / ((F.metric t₀).edist p (q i)).toReal) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ)
    (G : AncientPointedGeometricConvergence
      (fun _ => (FlowCarrier.ofConnectedManifold (m + 1) M).shrink)
      (fun i t => (F.interiorAncientRescaleAt (Q i) (hQ i) t₀).shrink.metric (t - δ))
      (fun i => equivShrink M (q i)) δ)
    (hGcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0)) :
    letI := G.limitCarrier.metricSpaceOf (G.limitFlow.metric 0)
    ∃ gamma : ℝ → G.limitCarrier.carrier, Isometry gamma ∧ gamma 0 = G.base := by
  let H := fun i => F.interiorAncientRescaleAt (Q i) (hQ i) t₀
  let L := fun i => r i * Real.sqrt (Q i)
  have htime (i : ℕ) (s : ℝ) (hs : s ≤ 0) : t₀ + s / Q i ≤ 0 :=
    (add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs (hQ i).le)).trans ht₀.le
  have hwindow (i : ℕ) (a : ℝ) : Icc a 0 ⊆ interior (Iio (-t₀ * Q i)) := by
    rw [isOpen_Iio.interior_eq]
    intro s hs
    exact hs.2.trans_lt (mul_pos (neg_pos.mpr ht₀) (hQ i))
  have hcH (i : ℕ) (s : ℝ) (hs : s ≤ 0) : MetricComplete ((H i).metric s) := by
    exact F.parabolicRescale_metricComplete _ _ _ _ _ _ _ (hcomplete _ (htime i s hs))
  have hoH (i : ℕ) (s : ℝ) (hs : s ≤ 0) (x : M) :
      ((H i).connection s).NonnegativeCurvatureOperator x := by
    exact F.parabolicRescale_nonnegativeCurvatureOperator _ _ _ _ _ _ _ _
      (hoperator _ (htime i s hs) x)
  have hmetric0 (i : ℕ) : (H i).metric 0 = rescaledMetric (F.metric t₀) (Q i) (hQ i) := by
    change rescaledMetric (F.metric (t₀ + 0 / Q i)) (Q i) (hQ i) = _
    rw [zero_div, add_zero]
  have hball (i : ℕ) : ((H i).metric 0).ball (q i) (L i) =
      (F.metric t₀).ball (q i) (r i) := by
    rw [hmetric0, rescaledMetric_ball_allDimensions]
    dsimp only [L]
    rw [mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr (hQ i)).ne']
  have hscalarH (i : ℕ) (s : ℝ) (hs : s ≤ 0) (x : M)
      (hx : x ∈ ((H i).metric 0).ball (q i) (L i)) :
      ((H i).connection s).scalarCurvature x ≤ 4 := by
    have hst : t₀ + s / Q i ≤ t₀ :=
      add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs (hQ i).le)
    have h := ((F.scalarCurvature_monotoneOn_of_bounded_ancient hC hcomplete
      hoperator hK hbound x) (hst.trans ht₀.le) ht₀.le hst).trans
        (hscalar i x ((hball i) ▸ hx))
    dsimp only [H, interiorAncientRescaleAt]
    rw [parabolicRescale_scalarCurvature]
    calc
      _ ≤ (Q i)⁻¹ * (4 * Q i) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (hQ i).le)
      _ = 4 := by field_simp [(hQ i).ne']
  have hRic (i : ℕ) (s : ℝ) (hs : s ≤ 0) (x : M)
      (v : TangentSpace (𝓡 (m + 1)) x) : 0 ≤ ((H i).connection s).ricci x v v :=
    (((H i).connection s).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus (m + 1) M ((H i).metric s) ((H i).connection s))
      x (hoH i s hs x) v).1
  have hupper (i : ℕ) (s : ℝ) (hs : s ∈ Icc (-δ) 0) (x : M)
      (hx : x ∈ ((H i).metric 0).ball (q i) (L i)) (v : TangentSpace (𝓡 (m + 1)) x) :
      ((H i).connection s).ricci x v v ≤ 4 * ((H i).metric s).inner x v v := by
    have hn : 0 ≤ ((H i).metric s).inner x v v := by
      let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
        ⟨((H i).metric s).toRiemannianMetric⟩
      exact @real_inner_self_nonneg (TangentSpace (𝓡 (m + 1)) x) _ _ v
    exact ((((H i).connection s).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus (m + 1) M ((H i).metric s) ((H i).connection s))
      x (hoH i s hs.2 x) v).2).trans
        (mul_le_mul_of_nonneg_right (hscalarH i s hs.2 x hx) hn)
  have hsec : (F.connection t₀).NonnegativeSectionalCurvature := by
    intro x v w
    exact (F.connection t₀).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hoperator t₀ ht₀.le x) v w
  obtain ⟨σ, hσ, s, minus, plus, hs, _, hstop, hbase, hminus, hplus, hangle⟩ :=
    (F.metric t₀).exists_selected_normalized_opposite_segments (F.connection t₀)
      (hcomplete t₀ ht₀.le) hsec p (fun i => q (G.subsequence i))
      (fun i => r (G.subsequence i)) (fun i => Q (G.subsequence i))
      (fun i => hr (G.subsequence i)) (fun i => hQ (G.subsequence i))
      (hdtop.comp G.subsequence_strictMono.tendsto_atTop)
      (hDtop.comp G.subsequence_strictMono.tendsto_atTop)
      (hLtop.comp G.subsequence_strictMono.tendsto_atTop)
      (hsmall.comp G.subsequence_strictMono.tendsto_atTop)
      (K := 4 * Real.exp (4 * δ)) (by positivity)
  apply exists_isometric_line_of_small_selected_terminal_segments hC hm
    (fun i => Iio (-t₀ * Q i)) H hδ (Λ := 4) (by norm_num) (scale := 1) (by norm_num)
    (fun i a => (hwindow i a).trans interior_subset) (fun i => hwindow i (-δ))
    (fun i t ht => hcH i t ht.2) (fun i t ht => hRic i t ht.2) q L hupper G hGcomplete
    σ hσ s (fun i => (hs i).1) (fun i => (hs i).2) minus plus
    (fun i => s i / 2) (fun i => s i / 2)
    (fun i => half_pos (hs i).1) (fun i => half_pos (hs i).1)
    (fun i => (hbase i).1) (fun i => (hbase i).2.1)
  · intro i a ha b hb
    rw [hmetric0]
    exact hminus i a ha b hb
  · intro i a ha b hb
    rw [hmetric0]
    exact hplus i a ha b hb
  · intro i
    rw [hmetric0]
    exact (hbase i).2.2.1
  · intro i
    rw [hmetric0]
    exact (hbase i).2.2.2
  · exact hstop
  · exact hstop
  · simpa only [hmetric0] using hangle
  · intro i α β A B hA hB hα0 hβ0 hα hβ
    let j := G.subsequence (σ i)
    have hsecH : ((H j).connection (-δ)).NonnegativeSectionalCurvature := by
      intro x v w
      exact ((H j).connection (-δ)).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
        x (hoH j (-δ) (by linarith) x) v w
    apply ((H j).metric (-δ)).toponogov_corresponding_side_of_edist_segments
      ((H j).connection (-δ)) (hcH j (-δ) (by linarith)) hsecH hA hB hα0 hβ0
    · intro a ha b hb
      rw [← ENNReal.ofReal_toReal (((H j).metric (-δ)).edist_ne_top _ _), hα a ha b hb]
    · intro a ha b hb
      rw [← ENNReal.ofReal_toReal (((H j).metric (-δ)).edist_ne_top _ _), hβ a ha b hb]

end PoincareConjecture.RicciFlow
