import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugeWeakLimit
import PoincareConjecture.Proofs.M08.IntegratedEnergy










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}



noncomputable def gaugePieceAction (e : AttainmentGauge G) {a b : ℝ}
    (gamma : ℝ → G.Point) (w : M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) a b) : ℝ :=
  (∫ s in a..b, (1 / 2 : ℝ) * gaugeLiftMetric e.index e.lift e.center (gamma s)
    (w s) (w s)) + ∫ s in a..b, 2 * s ^ 2 * horizontalScalarCurvature G.leafwise (gamma s)

set_option synthInstance.maxHeartbeats 200000 in




theorem finite_gauge_action_le (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {iota : Type*} [Fintype iota] (e : iota → AttainmentGauge G) (a b : iota → ℝ)
    (hab : ∀ i, a i ≤ b i) (K : iota → Set G.Point) (hK : ∀ i, IsCompact (K i))
    (hKU : ∀ i, K i ⊆ (e i).source)
    (paths : ℕ → ℝ → G.Point) (gamma : ℝ → G.Point)
    (hpaths : ∀ i k, ContinuousOn (paths k) (Icc (a i) (b i)))
    (hgamma : ∀ i, ContinuousOn gamma (Icc (a i) (b i)))
    (hpathsK : ∀ i k, MapsTo (paths k) (Icc (a i) (b i)) (K i))
    (hgammaK : ∀ i, MapsTo gamma (Icc (a i) (b i)) (K i))
    (hlim :
      let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel 3) : G.Point → Type _) :=
        ⟨(M14.auxiliarySpacetimeMetric G.spacetime).toRiemannianMetric⟩
      let : EMetricSpace G.Point := .ofRiemannianMetric (spacetimeModel 3) G.Point
      ∀ i, TendstoUniformlyOn paths gamma atTop (Icc (a i) (b i)))
    (v : ∀ i, ℕ → M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) (a i) (b i))
    (w : ∀ i, M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) (a i) (b i))
    (C : iota → ℝ) (hC : ∀ i, 0 ≤ C i) (hbound : ∀ i k, ‖v i k‖ ≤ C i)
    (hweak : ∀ i, ∀ l : M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) (a i) (b i) →L[ℝ] ℝ,
      Tendsto (fun k => l (v i k)) atTop (𝓝 (l (w i))))
    (action : ℕ → ℝ) (L : ℝ) (haction : Tendsto action atTop (𝓝 L))
    (henergy : ∀ k, (∑ i, gaugePieceAction (e i) (paths k) (v i k)) ≤ action k) :
    (∑ i, gaugePieceAction (e i) gamma (w i)) ≤ L := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel 3) : G.Point → Type _) :=
    ⟨(M14.auxiliarySpacetimeMetric G.spacetime).toRiemannianMetric⟩
  let : EMetricSpace G.Point := .ofRiemannianMetric (spacetimeModel 3) G.Point
  let : MetricSpace G.Point := UniformSpace.metricSpace G.Point
  have hlim' : ∀ i, TendstoUniformlyOn paths gamma atTop (Icc (a i) (b i)) := by
    with_reducible_and_instances exact hlim
  let A i q := (1 / 2 : ℝ) • gaugeLiftMetric (e i).index (e i).lift (e i).center q
  have hA (i : iota) : ContinuousOn (A i) (K i) :=
    (continuousOn_const : ContinuousOn (fun _ : G.Point => (1 / 2 : ℝ)) (K i)).smul
      ((gaugeLiftMetric_continuousOn (e i).index (e i).lift (e i).center
        (e i).smooth).mono (hKU i))
  let B i k s := A i (paths k s)
  let D i s := A i (gamma s)
  have hBcont (i : iota) (k : ℕ) : ContinuousOn (B i k) (Icc (a i) (b i)) :=
    (hA i).comp (hpaths i k) (fun s hs => hpathsK i k hs)
  have hDcont (i : iota) : ContinuousOn (D i) (Icc (a i) (b i)) :=
    (hA i).comp (hgamma i) (fun s hs => hgammaK i hs)
  have hB (i : iota) (k : ℕ) : MemLp (B i k) ∞ (volume.restrict (Icc (a i) (b i))) :=
    M08.continuousOn_memLp_top_Icc (f := B i k) (a := a i) (b := b i) (hBcont i k)
  have hD (i : iota) : MemLp (D i) ∞ (volume.restrict (Icc (a i) (b i))) :=
    M08.continuousOn_memLp_top_Icc (f := D i) (a := a i) (b := b i) (hDcont i)
  let Qk i k := M08.integratedFormMap _ ((hB i k).toLp (B i k))
  let Q i := M08.integratedFormMap _ ((hD i).toLp (D i))
  have hQ (i : iota) : Tendsto (fun k => ‖Qk i k - Q i‖) atTop (𝓝 (0 : ℝ)) := by
    apply M08.integratedForm_tendsto_of_uniform (B i) (D i) (hB i) (hD i)
    exact M08.uniform_composition_on_compact_core (hK i) (fun z : ℝ × G.Point => A i z.2)
      ((hA i).comp continuousOn_snd (fun _ hz => hz.2)) paths gamma
      (Eventually.of_forall (hpathsK i)) (hgammaK i) (hlim' i)
  have hQpos (i : iota) (z : M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) (a i) (b i)) :
      0 ≤ Q i z z := by
    apply M08.integratedForm_nonneg (hD i) _ z
    apply Eventually.of_forall
    intro s v
    change 0 ≤ (1 / 2 : ℝ) * gaugeLiftMetric (e i).index (e i).lift (e i).center
      (gamma s) v v
    apply mul_nonneg (by norm_num)
    rw [gaugeLiftMetric_apply]
    by_cases hv : v = 0
    · simp only [hv, map_zero, le_refl]
    · exact (((G.gaugeCover.metric (e i).index).metric
        ((e i).lift (gamma s)).1.val).pos ((e i).lift (gamma s)).2 v hv).le
  have hQeq (i : iota) (z : M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) (a i) (b i)) :
      Q i z z = ∫ s in a i..b i, D i s (z s) (z s) := by
    rw [intervalIntegral.integral_of_le (hab i), ← integral_Icc_eq_integral_Ioc]
    rw [M08.integratedFormMap_apply]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp
      (E := EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
      (f := D i) (hD i)] with s hs
    rw [hs]
  have hQkeq (i : iota) (k : ℕ) :
      Qk i k (v i k) (v i k) = ∫ s in a i..b i, B i k s (v i k s) (v i k s) := by
    rw [intervalIntegral.integral_of_le (hab i), ← integral_Icc_eq_integral_Ioc]
    rw [M08.integratedFormMap_apply]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp
      (E := EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
      (f := B i k) (hB i k)] with s hs
    rw [hs]
  let V : ℝ × G.Point → ℝ := fun z =>
    2 * z.1 ^ 2 * horizontalScalarCurvature G.leafwise z.2
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  have hV : Continuous V :=
    (continuous_const.mul (continuous_fst.pow 2)).mul
      (H.scalar_smooth.continuous.comp continuous_snd)
  have hpotential (i : iota) : Tendsto (fun k => ∫ s in a i..b i, V (s, paths k s)) atTop
      (𝓝 (∫ s in a i..b i, V (s, gamma s))) := by
    apply TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
    · apply Eventually.of_forall
      intro k
      rw [uIcc_of_le (hab i)]
      exact hV.continuousOn.comp (continuousOn_id.prodMk (hpaths i k))
        (fun _ _ => mem_univ _)
    · rw [uIcc_of_le (hab i)]
      exact M08.uniform_composition_on_compact_core (hK i) V hV.continuousOn paths gamma
        (Eventually.of_forall (hpathsK i)) (hgammaK i) (hlim' i)
  have htotal := M08.finite_quadratic_action_le v w C hC hbound hweak Q Qk hQpos hQ
    (fun k => ∑ i, ∫ s in a i..b i, V (s, paths k s)) action
    (∑ i, ∫ s in a i..b i, V (s, gamma s)) L
    (tendsto_finsetSum Finset.univ (fun i _ => hpotential i)) haction
    (fun k => by
      simpa only [hQkeq, ← Finset.sum_add_distrib, B, A, V, gaugePieceAction,
        smul_apply, smul_eq_mul] using henergy k)
  simpa only [hQeq, ← Finset.sum_add_distrib, D, A, V, gaugePieceAction,
    smul_apply, smul_eq_mul] using htotal

end PoincareConjecture.Proofs.M46
