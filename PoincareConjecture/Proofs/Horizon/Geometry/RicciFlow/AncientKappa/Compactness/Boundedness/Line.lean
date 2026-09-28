import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.BufferedSegments
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.AncientSolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.SelectedComparison

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

variable {M : Type} [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
  [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem exists_line_of_closed_selected_terminal_segments
    (P : M23NormalizedKappaCompactnessPredecessors)
    (F : ℕ → RicciFlow 3 M (Iic 0)) {δ : ℝ} (hδ : 0 < δ)
    (hc : ∀ i t, t ≤ 0 → MetricComplete ((F i).metric t))
    (hop : ∀ i t, t ≤ 0 → ∀ x, ((F i).connection t).NonnegativeCurvatureOperator x)
    (q : ℕ → M) (L : ℕ → ℝ)
    (hbound : ∀ i t, t ≤ 0 → ∀ x ∈ ((F i).metric 0).ball (q i) (L i),
      |((F i).connection t).curvatureTensorNorm x| ≤ 4)
    (G : AncientPointedGeometricConvergence
      (fun _ => FlowCarrier.ofConnectedManifold 3 M)
      (fun i t => (F i).metric (t - δ)) q δ)
    (hGcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0))
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (hmargin : ∀ i, 4 * Real.exp (12 * δ) * r i ≤ L (G.subsequence (σ i)))
    (minus plus : ℕ → ℝ → M) (a b : ℕ → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hm0 : ∀ i, minus i 0 = q (G.subsequence (σ i)))
    (hp0 : ∀ i, plus i 0 = q (G.subsequence (σ i)))
    (hm : ∀ i, ∀ s ∈ Icc (0 : ℝ) (a i), ∀ t ∈ Icc (0 : ℝ) (a i),
      (((F (G.subsequence (σ i))).metric 0).edist (minus i s) (minus i t)).toReal = |s - t|)
    (hp : ∀ i, ∀ s ∈ Icc (0 : ℝ) (b i), ∀ t ∈ Icc (0 : ℝ) (b i),
      (((F (G.subsequence (σ i))).metric 0).edist (plus i s) (plus i t)).toReal = |s - t|)
    (hx : ∀ i, minus i (a i) ∈
      ((F (G.subsequence (σ i))).metric 0).ball (q (G.subsequence (σ i))) (r i))
    (hy : ∀ i, plus i (b i) ∈
      ((F (G.subsequence (σ i))).metric 0).ball (q (G.subsequence (σ i))) (r i))
    (haTop : Tendsto a atTop atTop) (hbTop : Tendsto b atTop atTop)
    (hcos : Tendsto (fun i =>
      (a i ^ 2 + b i ^ 2 - (((F (G.subsequence (σ i))).metric 0).edist
        (minus i (a i)) (plus i (b i))).toReal ^ 2) / (2 * a i * b i)) atTop (𝓝 (-1))) :
    letI := G.limitCarrier.metricSpaceOf (G.limitFlow.metric 0)
    ∃ gamma : ℝ → G.limitCarrier.carrier, Isometry gamma ∧ gamma 0 = G.base := by
  have hRic (i : ℕ) (t : ℝ) (ht : t ≤ 0) (x : M) (v : TangentSpace (𝓡 3) x) :
      0 ≤ ((F i).connection t).ricci x v v :=
    (((F i).connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (P.tensor_calculus 3 M ((F i).metric t) ((F i).connection t)) x (hop i t ht x) v).1
  have hupper (i : ℕ) (t : ℝ) (ht : t ∈ Icc (-δ) 0) (x : M)
      (hx : x ∈ ((F i).metric 0).ball (q i) (L i)) (v : TangentSpace (𝓡 3) x) :
      ((F i).connection t).ricci x v v ≤ 12 * ((F i).metric t).inner x v v := by
    have hscalar := ((F i).connection t).scalarCurvature_le_curvatureTensorNorm_sharp x
    have hnorm := (le_abs_self _).trans (hbound i t ht.2 x hx)
    have hscalar' : ((F i).connection t).scalarCurvature x ≤ 12 := by
      norm_num at hscalar
      linarith
    have hn : 0 ≤ ((F i).metric t).inner x v v := by
      by_cases hv : v = 0
      · subst v; simp
      · exact (((F i).metric t).pos x v hv).le
    exact ((((F i).connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (P.tensor_calculus 3 M ((F i).metric t) ((F i).connection t))
      x (hop i t ht.2 x) v).2).trans (mul_le_mul_of_nonneg_right hscalar' hn)
  obtain ⟨hAB, hATop, hBTop, hangle, u, v, hend, hu, hv⟩ :=
    exists_buffered_opposite_segments_on_closed_ancient_flows (by norm_num : 0 < 2)
      (fun i => F (G.subsequence (σ i))) hδ (by norm_num : (0 : ℝ) ≤ 12)
      (by norm_num : (0 : ℝ) < 1)
      (fun i => hc (G.subsequence (σ i))) (fun i => hRic (G.subsequence (σ i)))
      (fun i => q (G.subsequence (σ i))) r (fun i => L (G.subsequence (σ i))) hr hmargin
      (fun i => hupper (G.subsequence (σ i))) minus plus a b ha hb hm0 hp0 hm hp
      hx hy haTop hbTop hcos
  let A := fun i => (((F (G.subsequence (σ i))).metric (-δ)).edist
    (q (G.subsequence (σ i))) (minus i (a i))).toReal
  let B := fun i => (((F (G.subsequence (σ i))).metric (-δ)).edist
    (q (G.subsequence (σ i))) (plus i (b i))).toReal
  have htime : ∀ c d : ℝ, d < δ → ∀ᶠ i : ℕ in atTop,
      Icc c d ⊆ (fun t : ℝ => t - δ) ⁻¹' Iic 0 := by
    intro c d hd
    exact Eventually.of_forall fun i t ht => by
      change t - δ ≤ 0
      linarith [ht.2]
  apply AncientPointedGeometricConvergence.exists_isometric_line_of_subsequence_opposite_segments
    (C := fun _ => FlowCarrier.ofConnectedManifold 3 M)
    (fun i => (F i).bufferedExpandingFlow δ) G hδ htime hGcomplete σ hσ u v
    (fun i => (hend i).1) (fun i => (hend i).2.2.1) hATop hBTop
  · simpa only [bufferedExpandingFlow_metric, zero_sub] using hu
  · simpa only [bufferedExpandingFlow_metric, zero_sub] using hv
  · simp only [bufferedExpandingFlow_metric, zero_sub]
    change Tendsto (fun i =>
      (A i ^ 2 + B i ^ 2 - (((F (G.subsequence (σ i))).metric (-δ)).edist
        (u i (A i)) (v i (B i))).toReal ^ 2) / (2 * A i * B i)) atTop (𝓝 (-1))
    simpa only [A, B, (hend _).2.1, (hend _).2.2.2] using hangle
  · intro i s hs t ht
    simp only [bufferedExpandingFlow_metric, zero_sub]
    let j := G.subsequence (σ i)
    have hsec : ((F j).connection (-δ)).NonnegativeSectionalCurvature := by
      intro x v w
      exact ((F j).connection (-δ)).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
        x (hop j (-δ) (by linarith) x) v w
    apply ((F j).metric (-δ)).toponogov_corresponding_side_of_edist_segments
      ((F j).connection (-δ)) (hc j (-δ) (by linarith)) hsec (hAB i).1 (hAB i).2
      (hend i).1 (hend i).2.2.1 ?_ ?_ s hs t ht
    · intro s hs t ht
      rw [← ENNReal.ofReal_toReal (((F j).metric (-δ)).edist_ne_top _ _), hu i s hs t ht]
    · intro s hs t ht
      rw [← ENNReal.ofReal_toReal (((F j).metric (-δ)).edist_ne_top _ _), hv i s hs t ht]

theorem exists_line_of_closed_selected_rescalings
    (P : M23NormalizedKappaCompactnessPredecessors)
    {b : ℝ} (F : RicciFlow 3 M (Iic b))
    (hc : MetricComplete (F.metric b))
    (hop : ∀ x, (F.connection b).NonnegativeCurvatureOperator x)
    (p : M) (q : ℕ → M) (r Q : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hQ : ∀ i, 0 < Q i)
    (H : ℕ → RicciFlow 3 M (Iic 0))
    (hcal : ∀ i s, MetricHomothetyCalculus (F.metric (b + s / Q i))
      ((H i).metric s) (Diffeomorph.refl (𝓡 3) M ∞) (Q i))
    (hcH : ∀ i t, t ≤ 0 → MetricComplete ((H i).metric t))
    (hopH : ∀ i t, t ≤ 0 → ∀ x, ((H i).connection t).NonnegativeCurvatureOperator x)
    (hbound : ∀ i t, t ≤ 0 → ∀ x ∈ ((H i).metric 0).ball (q i) (r i * Real.sqrt (Q i)),
      |((H i).connection t).curvatureTensorNorm x| ≤ 4)
    (hdtop : Tendsto (fun i => ((F.metric b).edist p (q i)).toReal) atTop atTop)
    (hDtop : Tendsto (fun i => ((F.metric b).edist p (q i)).toReal * Real.sqrt (Q i))
      atTop atTop)
    (hLtop : Tendsto (fun i => r i * Real.sqrt (Q i)) atTop atTop)
    (hsmall : Tendsto (fun i => r i / ((F.metric b).edist p (q i)).toReal) atTop (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ)
    (G : AncientPointedGeometricConvergence
      (fun _ => FlowCarrier.ofConnectedManifold 3 M)
      (fun i t => (H i).metric (t - δ)) q δ)
    (hGcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0)) :
    letI := G.limitCarrier.metricSpaceOf (G.limitFlow.metric 0)
    ∃ gamma : ℝ → G.limitCarrier.carrier, Isometry gamma ∧ gamma 0 = G.base := by
  have hed (i : ℕ) (x y : M) : ((H i).metric 0).edist x y =
      (rescaledMetric (F.metric b) (Q i) (hQ i)).edist x y := by
    rw [rescaledMetric_edist]
    have h := (hcal i 0).edist_eq x y
    change ((H i).metric 0).edist x y =
      ENNReal.ofReal (Real.sqrt (Q i)) * (F.metric (b + 0 / Q i)).edist x y at h
    rwa [zero_div, add_zero] at h
  have hsec : (F.connection b).NonnegativeSectionalCurvature := by
    intro x v w
    exact (F.connection b).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hop x) v w
  obtain ⟨σ, hσ, s, minus, plus, hs, _, hstop, hbase, hminus, hplus, hangle⟩ :=
    (F.metric b).exists_selected_normalized_opposite_segments (F.connection b) hc hsec p
      (fun i => q (G.subsequence i)) (fun i => r (G.subsequence i))
      (fun i => Q (G.subsequence i)) (fun i => hr (G.subsequence i))
      (fun i => hQ (G.subsequence i))
      (hdtop.comp G.subsequence_strictMono.tendsto_atTop)
      (hDtop.comp G.subsequence_strictMono.tendsto_atTop)
      (hLtop.comp G.subsequence_strictMono.tendsto_atTop)
      (hsmall.comp G.subsequence_strictMono.tendsto_atTop)
      (K := 4 * Real.exp (12 * δ)) (by positivity)
  apply exists_line_of_closed_selected_terminal_segments P H hδ hcH hopH q
    (fun i => r i * Real.sqrt (Q i)) hbound G hGcomplete σ hσ s
    (fun i => (hs i).1) (fun i => (hs i).2) minus plus
    (fun i => s i / 2) (fun i => s i / 2)
    (fun i => half_pos (hs i).1) (fun i => half_pos (hs i).1)
    (fun i => (hbase i).1) (fun i => (hbase i).2.1)
  · intro i a ha b hb
    rw [hed]
    exact hminus i a ha b hb
  · intro i a ha b hb
    rw [hed]
    exact hplus i a ha b hb
  · intro i
    change ((H (G.subsequence (σ i))).metric 0).edist
      (q (G.subsequence (σ i))) (minus i (s i / 2)) < ENNReal.ofReal (s i)
    rw [hed]
    exact (hbase i).2.2.1
  · intro i
    change ((H (G.subsequence (σ i))).metric 0).edist
      (q (G.subsequence (σ i))) (plus i (s i / 2)) < ENNReal.ofReal (s i)
    rw [hed]
    exact (hbase i).2.2.2
  · exact hstop
  · exact hstop
  · simpa only [hed] using hangle

end PoincareConjecture.RicciFlow
