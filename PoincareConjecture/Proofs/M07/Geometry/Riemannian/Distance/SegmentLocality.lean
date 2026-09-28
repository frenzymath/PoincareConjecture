import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.IntrinsicMinimizer

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem continuousOn_of_edist_segment
    (g : RiemannianMetric n M) {η : ℝ → M} {d : ℝ≥0∞} (hd : d ≠ ⊤)
    (hη : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (η s) (η t) = ENNReal.ofReal |s - t| * d) :
    ContinuousOn η (Icc (0 : ℝ) 1) := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  apply LipschitzOnWith.continuousOn (K := d.toNNReal)
  intro s hs t ht
  change g.edist (η s) (η t) ≤ _
  rw [hη s hs t ht, ENNReal.coe_toNNReal hd, edist_dist, Real.dist_eq, mul_comm]

theorem exists_local_point_of_edist_segment
    (g : RiemannianMetric n M) {η : ℝ → M} {p q : M}
    (h0 : η 0 = p) (h1 : η 1 = q)
    (hd0 : 0 < g.edist p q) (hd : g.edist p q ≠ ⊤)
    (hη : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (η s) (η t) = ENNReal.ofReal |s - t| * g.edist p q)
    {U : Set M} (hU : U ∈ 𝓝 p) {r : ℝ} (hr : 0 < r) :
    ∃ z ∈ U, 0 < g.edist p z ∧ g.edist p z < ENNReal.ofReal r ∧
      g.edist p q = g.edist p z + g.edist z q := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n)) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  have hc := g.continuousOn_of_edist_segment hd hη 0 (by simp)
  have hnear : ∀ᶠ t in 𝓝[Icc (0 : ℝ) 1] 0,
      η t ∈ U ∧ g.edist p (η t) < ENNReal.ofReal r := by
    have hnb : U ∩ Metric.eball p (ENNReal.ofReal r) ∈ 𝓝 (η 0) := by
      rw [h0]
      exact inter_mem hU (Metric.eball_mem_nhds p (ENNReal.ofReal_pos.mpr hr))
    have hnear' : ∀ᶠ t in 𝓝[Icc (0 : ℝ) 1] 0,
        η t ∈ U ∩ Metric.eball p (ENNReal.ofReal r) := hc hnb
    filter_upwards [hnear'] with t ht
    exact ⟨ht.1, by change EDist.edist p (η t) < _; rw [edist_comm]; exact ht.2⟩
  have hfilter : 𝓝[>] (0 : ℝ) ≤ 𝓝[Icc (0 : ℝ) 1] 0 := by
    rw [nhdsWithin_Icc_eq_nhdsGE (by norm_num : (0 : ℝ) < 1)]
    exact nhdsWithin_mono 0 Ioi_subset_Ici_self
  have hlt1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, htnear, htpos, ht1⟩ :=
    ((hnear.filter_mono hfilter).and (hpos.and hlt1)).exists
  have ht : t ∈ Icc (0 : ℝ) 1 := ⟨htpos.le, ht1.le⟩
  have hpt : g.edist p (η t) = ENNReal.ofReal t * g.edist p q := by
    simpa only [h0, zero_sub, abs_neg, abs_of_nonneg ht.1] using
      hη 0 (by simp) t ht
  have htq : g.edist (η t) q = ENNReal.ofReal (1 - t) * g.edist p q := by
    simpa only [h1, abs_of_nonpos (sub_nonpos.mpr ht.2), neg_sub] using
      hη t ht 1 (by simp)
  refine ⟨η t, htnear.1, ?_, htnear.2, ?_⟩
  · rw [hpt]
    exact ENNReal.mul_pos (ne_of_gt (ENNReal.ofReal_pos.mpr htpos)) (ne_of_gt hd0)
  · rw [hpt, htq, ← add_mul, ← ENNReal.ofReal_add ht.1 (sub_nonneg.mpr ht.2)]
    simp

theorem exists_local_minimizing_step_of_precompact_ball
    (g : RiemannianMetric n M) (p q : M) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (closure (g.ball p R)))
    (hq : q ∈ g.ball p R) (hd : 0 < g.edist p q)
    {U : Set M} (hU : U ∈ 𝓝 p) {r : ℝ} (hr : 0 < r) :
    ∃ z ∈ U, 0 < g.edist p z ∧ g.edist p z < ENNReal.ofReal r ∧
      g.edist p q = g.edist p z + g.edist z q := by
  obtain ⟨η, h0, h1, _, hη⟩ :=
    g.exists_intrinsic_metric_segment_of_precompact_ball p q hR hcompact hq
  exact g.exists_local_point_of_edist_segment h0 h1 hd
    (ne_top_of_lt (hq.trans_le le_top)) hη hU hr

omit [T2Space M] in

theorem exists_precompact_ball_of_edist_add_eq
    (g : RiemannianMetric n M) (p x q : M) {R : ℝ}
    (hcompact : IsCompact (closure (g.ball p R))) (hq : q ∈ g.ball p R)
    (hadd : g.edist p x + g.edist x q = g.edist p q) :
    ∃ r : ℝ, 0 < r ∧ IsCompact (closure (g.ball x r)) ∧ q ∈ g.ball x r := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hfinite : g.edist p q ≠ ⊤ := ne_top_of_lt (hq.trans_le le_top)
  have hxfinite : g.edist p x ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite (hadd ▸ le_add_right le_rfl)
  have hxqfinite : g.edist x q ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite (hadd ▸ le_add_left le_rfl)
  have hreal : (g.edist p x).toReal + (g.edist x q).toReal =
      (g.edist p q).toReal := by
    rw [← ENNReal.toReal_add hxfinite hxqfinite, hadd]
  have hdistR : (g.edist p q).toReal < R := ENNReal.toReal_lt_of_lt_ofReal hq
  let r := R - (g.edist p x).toReal
  have hr : 0 < r := by
    dsimp [r]
    linarith [ENNReal.toReal_nonneg (a := g.edist x q)]
  have hsum : g.edist p x + ENNReal.ofReal r = ENNReal.ofReal R := by
    rw [← ENNReal.ofReal_toReal hxfinite,
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg hr.le]
    congr 1
    dsimp [r]
    ring
  refine ⟨r, hr, ?_, ?_⟩
  · apply hcompact.of_isClosed_subset isClosed_closure
    apply closure_mono
    intro y hy
    exact (Manifold.riemannianEDist_triangle (I := 𝓡 n) (x := p) (y := x) (z := y)).trans_lt
      ((ENNReal.add_lt_add_left hxfinite hy).trans_eq hsum)
  · change g.edist x q < ENNReal.ofReal r
    rw [← ENNReal.ofReal_toReal hxqfinite]
    apply (ENNReal.ofReal_lt_ofReal_iff hr).mpr
    dsimp [r]
    linarith

end PoincareConjecture.RiemannianMetric
