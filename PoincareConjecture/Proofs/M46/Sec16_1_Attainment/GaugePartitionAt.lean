import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugeOverlapPartition
import PoincareConjecture.Proofs.M08.ChartCoverAt

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}

theorem exists_compact_gauge_partition_at {a b s : ℝ} (hs : s ∈ Ioo a b)
    (gamma : ℝ → G.Point) (hgamma : Continuous gamma) (paths : ℕ → ℝ → G.Point)
    (hlim :
      let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel 3) : G.Point → Type _) :=
        ⟨(M14.auxiliarySpacetimeMetric G.spacetime).toRiemannianMetric⟩
      let : EMetricSpace G.Point := .ofRiemannianMetric (spacetimeModel 3) G.Point
      TendstoUniformlyOn paths gamma atTop (Icc a b)) :
    ∃ (m : ℕ) (t : Fin (m + 1) → ℝ) (e : Fin m → AttainmentGauge G)
      (l r : Fin m → ℝ) (K : Fin m → Set G.Point) (N : ℕ) (j : Fin m),
      Monotone t ∧ t 0 = a ∧ t (Fin.last m) = b ∧
      (∀ i, a ≤ l i ∧ l i < r i ∧ r i ≤ b ∧ l i ≤ t i.castSucc ∧ t i.succ ≤ r i ∧
        IsCompact (K i) ∧ gamma '' Icc (l i) (r i) ⊆ interior (K i) ∧
        K i ⊆ (e i).source ∧
        ∀ z ∈ Icc (t i.castSucc) (t i.succ), Icc (l i) (r i) ∈ 𝓝[Icc a b] z) ∧
      (∀ k ≥ N, ∀ i, MapsTo (paths k) (Icc (l i) (r i)) (K i)) ∧
      a < t j.castSucc ∧ t j.castSucc < s ∧ s < t j.succ ∧ t j.succ < b := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel 3) : G.Point → Type _) :=
    ⟨(M14.auxiliarySpacetimeMetric G.spacetime).toRiemannianMetric⟩
  let : EMetricSpace G.Point := .ofRiemannianMetric (spacetimeModel 3) G.Point
  let metric : MetricSpace G.Point := UniformSpace.metricSpace G.Point
  let : EMetricSpace G.Point := metric.toEMetricSpace
  let : LocallyCompactSpace G.Point :=
    Manifold.locallyCompact_of_finiteDimensional (M := G.Point) (spacetimeModel 3)
  have hlim' : TendstoUniformlyOn paths gamma atTop (Icc a b) := by
    with_reducible_and_instances exact hlim
  obtain ⟨m, t, e, K, j, ht, hta, htb, hK, hanchor⟩ :=
    M08.exists_compact_partition_at (fun e : AttainmentGauge G => e.source)
      (fun e => e.source_open) exists_attainmentGauge hs gamma hgamma
  have hab : a < b := hs.1.trans hs.2
  have hleft (i : Fin m) : a ≤ t i.castSucc := hta ▸ ht (Fin.zero_le _)
  have hright (i : Fin m) : t i.succ ≤ b := htb ▸ ht (Fin.le_last _)
  choose l r hp using fun i : Fin m => M08.exists_enlarged_closed_interval hab
    (hleft i) (ht (Fin.castSucc_le_succ i)) (hright i)
    (isOpen_interior.preimage hgamma)
    (fun z hz => (hK i).2.1 (mem_image_of_mem gamma hz))
  have hgammaK (i : Fin m) : gamma '' Icc (l i) (r i) ⊆ interior (K i) := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hp i).2.2.2.2.2.1 hz
  have htail (i : Fin m) : ∀ᶠ k in atTop, MapsTo (paths k) (Icc (l i) (r i)) (K i) := by
    obtain ⟨delta, hdelta, hmargin⟩ := (isCompact_Icc.image hgamma).exists_cthickening_subset_open
      isOpen_interior (hgammaK i)
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim' delta hdelta] with k hk
    intro z hz
    have hzab : z ∈ Icc a b := ⟨(hp i).1.trans hz.1, hz.2.trans (hp i).2.2.1⟩
    apply interior_subset (hmargin ?_)
    exact Metric.mem_cthickening_of_dist_le (paths k z) (gamma z) delta _
      (mem_image_of_mem gamma hz) (by simpa only [dist_comm] using (hk z hzab).le)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Filter.eventually_all.mpr htail)
  refine ⟨m, t, e, l, r, K, N, j, ht, hta, htb, ?_, hN, hanchor⟩
  intro i
  obtain ⟨hal, hlr, hrb, hlt, htr, _, hnear⟩ := hp i
  exact ⟨hal, hlr, hrb, hlt, htr, (hK i).1, hgammaK i, (hK i).2.2, hnear⟩

end PoincareConjecture.Proofs.M46
