import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugePartition
import PoincareConjecture.Proofs.M08.OverlappingIntervals

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}

theorem exists_compact_overlapping_gauge_partition {a b : ℝ} (hab : a < b)
    (gamma : ℝ → G.Point) (hgamma : Continuous gamma) (paths : ℕ → ℝ → G.Point)
    (hlim :
      let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel 3) : G.Point → Type _) :=
        ⟨(M14.auxiliarySpacetimeMetric G.spacetime).toRiemannianMetric⟩
      let : EMetricSpace G.Point := .ofRiemannianMetric (spacetimeModel 3) G.Point
      TendstoUniformlyOn paths gamma atTop (Icc a b)) :
    ∃ (m : ℕ) (t : Fin (m + 1) → ℝ) (e : Fin m → AttainmentGauge G)
      (l r : Fin m → ℝ) (K : Fin m → Set G.Point) (N : ℕ),
      0 < m ∧ Monotone t ∧ t 0 = a ∧ t (Fin.last m) = b ∧
      (∀ i, a ≤ l i ∧ l i < r i ∧ r i ≤ b ∧ l i ≤ t i.castSucc ∧ t i.succ ≤ r i ∧
        IsCompact (K i) ∧ gamma '' Icc (l i) (r i) ⊆ interior (K i) ∧
        K i ⊆ (e i).source ∧
        ∀ s ∈ Icc (t i.castSucc) (t i.succ), Icc (l i) (r i) ∈ 𝓝[Icc a b] s) ∧
      ∀ k ≥ N, ∀ i, MapsTo (paths k) (Icc (l i) (r i)) (K i) := by
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
  let U : AttainmentGauge G → Set ℝ := fun e => gamma ⁻¹' e.source
  have hU : ∀ e, IsOpen (U e) := fun e => e.source_open.preimage hgamma
  have hcover : Icc a b ⊆ ⋃ e, U e := by
    intro s _
    obtain ⟨e, he⟩ := exists_attainmentGauge (gamma s)
    exact mem_iUnion.mpr ⟨e, he⟩
  obtain ⟨m, t, e, l, r, hm, ht, hta, htb, hp⟩ :=
    M08.exists_overlapping_Icc_partition U hU hab hcover
  have hsrc (i : Fin m) : gamma '' Icc (l i) (r i) ⊆ (e i).source := by
    rintro _ ⟨s, hs, rfl⟩
    exact (hp i).2.2.2.2.2.1 hs
  have hcompact (i : Fin m) : IsCompact (gamma '' Icc (l i) (r i)) :=
    isCompact_Icc.image hgamma
  choose K hK hgammaK hKU using fun i =>
    exists_compact_between (hcompact i) (e i).source_open (hsrc i)
  have htail (i : Fin m) : ∀ᶠ k in atTop, MapsTo (paths k) (Icc (l i) (r i)) (K i) := by
    obtain ⟨delta, hdelta, hmargin⟩ := (hcompact i).exists_cthickening_subset_open
      isOpen_interior (hgammaK i)
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim' delta hdelta] with k hk
    intro s hs
    have hsab : s ∈ Icc a b := ⟨(hp i).1.trans hs.1, hs.2.trans (hp i).2.2.1⟩
    have hnear : paths k s ∈ Metric.cthickening delta (gamma '' Icc (l i) (r i)) := by
      exact Metric.mem_cthickening_of_dist_le (paths k s) (gamma s) delta _
        (mem_image_of_mem gamma hs) (by simpa only [dist_comm] using (hk s hsab).le)
    exact interior_subset (hmargin hnear)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Filter.eventually_all.mpr htail)
  refine ⟨m, t, e, l, r, K, N, hm, ht, hta, htb, ?_, hN⟩
  intro i
  obtain ⟨hal, hlr, hrb, hlt, htr, _, hnear⟩ := hp i
  exact ⟨hal, hlr, hrb, hlt, htr, hK i, hgammaK i, hKU i, hnear⟩

end PoincareConjecture.Proofs.M46
