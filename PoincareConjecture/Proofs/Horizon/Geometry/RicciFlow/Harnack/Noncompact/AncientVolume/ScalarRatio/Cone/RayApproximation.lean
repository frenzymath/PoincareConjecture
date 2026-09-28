import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Cone.MinimizingRay

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Metric Set
open scoped Topology Manifold ContDiff Bundle ENNReal

namespace Poincare.AncientVolume.ScalarRatio

private theorem exists_ray_approximating_of_minimizing_segments
    {X : Type*} [MetricSpace X] [ProperSpace X] (p : X) (x : ℕ → X)
    (hescape : Tendsto (fun i => dist p (x i)) atTop atTop)
    (γ : ℕ → ℝ → X) (hγ0 : ∀ i, γ i 0 = p) (hγ1 : ∀ i, γ i 1 = x i)
    (hγ : ∀ i, ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (γ i s) (γ i t) = |s - t| * dist p (x i))
    (hcomparison : ∀ a : ℝ, 0 < a → ∀ α β : ℝ → X,
      α 0 = p → β 0 = p →
      (∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) a,
        dist (α s) (α t) = |s - t|) →
      (∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) a,
        dist (β s) (β t) = |s - t|) →
      ∀ s ∈ Icc (0 : ℝ) a,
        (s / a) ^ 2 * dist (α a) (β a) ^ 2 ≤ dist (α s) (β s) ^ 2) :
    ∃ ray : ℝ → X, ray 0 = p ∧
      (∀ s, 0 ≤ s → ∀ t, 0 ≤ t → dist (ray s) (ray t) = |s - t|) ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun i => dist (x (σ i)) (ray (dist p (x (σ i)))) /
          dist p (x (σ i))) atTop (𝓝 0) := by
  classical
  let radius : ℕ → ℝ := fun i => dist p (x i)
  let arc : ℕ → ℝ → X := fun i t => γ i (t / radius i)
  have hbase (i : ℕ) : arc i 0 = p := by simp only [arc, zero_div, hγ0]
  have hunit (i : ℕ) (hi : 0 < radius i) :
      ∀ s ∈ Icc (0 : ℝ) (radius i), ∀ t ∈ Icc (0 : ℝ) (radius i),
        dist (arc i s) (arc i t) = |s - t| := by
    intro s hs t ht
    change dist (γ i (s / radius i)) (γ i (t / radius i)) = _
    rw [hγ i (s / radius i)
      ⟨div_nonneg hs.1 hi.le, (div_le_one hi).mpr hs.2⟩ (t / radius i)
      ⟨div_nonneg ht.1 hi.le, (div_le_one hi).mpr ht.2⟩,
      ← sub_div, abs_div, abs_of_pos hi]
    exact div_mul_cancel₀ _ hi.ne'
  have hdist : ∀ s t : Ici (0 : ℝ),
      Tendsto (fun i => dist (arc i s) (arc i t)) atTop (𝓝 |s.val - t.val|) := by
    intro s t
    apply tendsto_const_nhds.congr'
    filter_upwards [hescape.eventually_ge_atTop s.val,
      hescape.eventually_ge_atTop t.val, hescape.eventually_ge_atTop 1] with i hs ht hi
    exact (hunit i (zero_lt_one.trans_le hi) s ⟨s.property, hs⟩ t ⟨t.property, ht⟩).symm
  have hbounded : ∀ t : Ici (0 : ℝ), ∀ᶠ i in (hyperfilter ℕ : Filter ℕ),
      arc i t ∈ closedBall p (t.val + 1) := by
    intro t
    have hlim : Tendsto (fun i => dist (arc i t) p) atTop (𝓝 t.val) := by
      simpa only [hbase, sub_zero, abs_of_nonneg (show 0 ≤ t.val from t.property)] using
        hdist t ⟨0, by simp⟩
    have hbound := hlim.eventually (eventually_lt_nhds (by linarith : t.val < t.val + 1))
    filter_upwards [hbound.filter_mono Nat.hyperfilter_le_atTop] with i hi
    exact hi.le
  have hlimit : ∀ t : Ici (0 : ℝ), ∃ q : X,
      Tendsto (fun i => arc i t) (hyperfilter ℕ : Filter ℕ) (𝓝 q) := by
    intro t
    obtain ⟨q, _, hq⟩ := (isCompact_closedBall p (t.val + 1)).ultrafilter_le_nhds'
      ((hyperfilter ℕ).map fun i => arc i t) (hbounded t)
    rw [Ultrafilter.coe_map] at hq
    exact ⟨q, hq⟩
  choose limit hlimit using hlimit
  have hlimitdist (s t : Ici (0 : ℝ)) : dist (limit s) (limit t) = |s.val - t.val| :=
    tendsto_nhds_unique ((hlimit s).dist (hlimit t))
      ((hdist s t).mono_left Nat.hyperfilter_le_atTop)
  have hlimit0 : limit ⟨0, by simp⟩ = p := by
    have hconst : Tendsto (fun i => arc i 0) (hyperfilter ℕ : Filter ℕ) (𝓝 p) := by
      simpa only [hbase] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => p)
          (hyperfilter ℕ : Filter ℕ) (𝓝 p))
    exact tendsto_nhds_unique (hlimit ⟨0, by simp⟩) hconst
  let ray : ℝ → X := fun t => limit ⟨max t 0, by exact le_max_right t (0 : ℝ)⟩
  have hray0 : ray 0 = p := by simpa only [ray, max_self] using hlimit0
  have hray : ∀ s, 0 ≤ s → ∀ t, 0 ≤ t → dist (ray s) (ray t) = |s - t| := by
    intro s hs t ht
    simpa only [ray, max_eq_left hs, max_eq_left ht] using hlimitdist ⟨s, hs⟩ ⟨t, ht⟩
  have hone : MapClusterPt (ray 1) atTop (fun i => arc i 1) := by
    have h := (hlimit ⟨1, by norm_num⟩).mapClusterPt.mono Nat.hyperfilter_le_atTop
    simpa only [ray, max_eq_left zero_le_one] using h
  obtain ⟨σ, hσ, hσlim⟩ := hone.tendsto_subseq
  refine ⟨ray, hray0, hray, σ, hσ, ?_⟩
  have herror : Tendsto (fun i => dist (arc (σ i) 1) (ray 1)) atTop (𝓝 0) := by
    simpa only [dist_self, Function.comp_apply] using
      hσlim.dist (tendsto_const_nhds (x := ray 1))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds herror
  · exact Eventually.of_forall (fun i => div_nonneg dist_nonneg dist_nonneg)
  · filter_upwards [(hescape.comp hσ.tendsto_atTop).eventually_ge_atTop 1] with i hi
    have hpos : 0 < radius (σ i) := zero_lt_one.trans_le hi
    have h := hcomparison (radius (σ i)) hpos (arc (σ i)) ray (hbase _) hray0
      (hunit _ hpos) (fun s hs t ht => hray s hs.1 t ht.1) 1 ⟨zero_le_one, hi⟩
    have hend : arc (σ i) (radius (σ i)) = x (σ i) := by
      simp only [arc, div_self hpos.ne', hγ1]
    rw [hend] at h
    have hsquare : (dist (x (σ i)) (ray (radius (σ i))) / radius (σ i)) ^ 2 ≤
        dist (arc (σ i) 1) (ray 1) ^ 2 := by
      convert h using 1; ring
    exact (sq_le_sq₀ (div_nonneg dist_nonneg hpos.le) dist_nonneg).mp hsquare

end Poincare.AncientVolume.ScalarRatio

namespace PoincareConjecture.RiemannianMetric

theorem exists_minimizing_ray_approximating_escaping_sequence
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [ConnectedSpace M]
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M) (x : ℕ → M)
    (hescape : Tendsto (fun i => (g.edist p (x i)).toReal) atTop atTop)
    (hcomparison : ∀ a : ℝ, 0 < a → ∀ α β : ℝ → M,
      α 0 = p → β 0 = p →
      (∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) a,
        g.edist (α s) (α t) = ENNReal.ofReal |s - t|) →
      (∀ s ∈ Icc (0 : ℝ) a, ∀ t ∈ Icc (0 : ℝ) a,
        g.edist (β s) (β t) = ENNReal.ofReal |s - t|) →
      ∀ s ∈ Icc (0 : ℝ) a,
        (s / a) ^ 2 * (g.edist (α a) (β a)).toReal ^ 2 ≤
          (g.edist (α s) (β s)).toReal ^ 2) :
    ∃ ray : ℝ → M, ray 0 = p ∧
      (∀ s, 0 ≤ s → ∀ t, 0 ≤ t →
        g.edist (ray s) (ray t) = ENNReal.ofReal |s - t|) ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧
        Tendsto (fun i => (g.edist (x (σ i))
          (ray ((g.edist p (x (σ i))).toReal))).toReal /
            (g.edist p (x (σ i))).toReal) atTop (𝓝 0) := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : MetricSpace M := EMetricSpace.toMetricSpace g.edist_ne_top
  let : ProperSpace M := ProperSpace.of_isCompact_closedBall_of_le 0 (fun y r hr => by
    have hset : closedBall y r = {z | g.edist y z ≤ ENNReal.ofReal r} := by
      ext z
      change dist z y ≤ r ↔ g.edist y z ≤ ENNReal.ofReal r
      rw [dist_comm]
      exact (edist_le_ofReal hr).symm
    rw [hset]
    exact g.isCompact_closedBall_of_metricComplete hc y r)
  have hsegments : ∀ i : ℕ, ∃ γ : ℝ → M, γ 0 = p ∧ γ 1 = x i ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist p (x i) := by
    intro i
    obtain ⟨ε, _, γ, _, hγ0, hγ1, hγ⟩ :=
      g.exists_minimizing_geodesic_of_metricComplete hc p (x i)
    refine ⟨γ, hγ0, hγ1, ?_⟩
    intro s hs t ht
    change (g.edist (γ s) (γ t)).toReal = |s - t| * (g.edist p (x i)).toReal
    rw [hγ s hs t ht, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)]
  choose γ hγ0 hγ1 hγ using hsegments
  obtain ⟨ray, hray0, hray, σ, hσ, hlim⟩ :=
    Poincare.AncientVolume.ScalarRatio.exists_ray_approximating_of_minimizing_segments
      p x hescape γ hγ0 hγ1 hγ (by
        intro a ha α β hα0 hβ0 hα hβ s hs
        apply hcomparison a ha α β hα0 hβ0
        · intro u hu v hv
          change EDist.edist (α u) (α v) = _
          rw [edist_dist, hα u hu v hv]
        · intro u hu v hv
          change EDist.edist (β u) (β v) = _
          rw [edist_dist, hβ u hu v hv]
        · exact hs)
  refine ⟨ray, hray0, ?_, σ, hσ, hlim⟩
  intro s hs t ht
  change EDist.edist (ray s) (ray t) = _
  rw [edist_dist, hray s hs t ht]

end PoincareConjecture.RiemannianMetric
