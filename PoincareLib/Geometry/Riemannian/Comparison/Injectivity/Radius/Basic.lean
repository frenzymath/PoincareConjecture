import PoincareLib.Geometry.Riemannian.Geodesic.Complete
import PoincareLib.Geometry.Riemannian.Coordinates.Exponential.Gauss.Manifold

/-!
# The canonical exponential and its truncated injectivity radius

Completeness supplies a global geodesic for every initial velocity. Uniqueness
makes its time-one endpoint independent of the choice. The injectivity radius
truncated at a finite positive scale is the supremum of the radii, below that
scale, on which this exponential is injective. Local exponential charts prove
that this radius is positive at each point.

The truncation is the one used in Maeder--Baumdicker--Seidel,
arXiv:2310.03369v3, Corollary 4.21, p. 34, and Lemmas 5.1--5.2, pp. 35--37.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The complete geodesic with prescribed initial coordinate velocity. -/
noncomputable def globalGeodesic (g : RiemannianMetric n M)
    (hc : MetricComplete g) (p : M) (v : EuclideanSpace ℝ (Fin n)) : ℝ → M :=
  Classical.choose (g.exists_global_geodesic hc p v)

theorem globalGeodesic_spec (g : RiemannianMetric n M)
    (hc : MetricComplete g) (p : M) (v : EuclideanSpace ℝ (Fin n)) :
    g.IsGeodesicOn (g.globalGeodesic hc p v) univ ∧
      g.globalGeodesic hc p v 0 = p ∧
      HasDerivAt (fun t => extChartAt (𝓡 n) p (g.globalGeodesic hc p v t)) v 0 :=
  Classical.choose_spec (g.exists_global_geodesic hc p v)

/-- The time-one endpoint of the complete geodesic with initial velocity `v`. -/
noncomputable def globalExponential (g : RiemannianMetric n M)
    (hc : MetricComplete g) (p : M) (v : EuclideanSpace ℝ (Fin n)) : M :=
  g.globalGeodesic hc p v 1

/-- Geodesic uniqueness identifies the selected exponential with any geodesic
having the prescribed initial data. -/
theorem globalExponential_eq_endpoint (g : RiemannianMetric n M)
    (hc : MetricComplete g) (p : M) (v : EuclideanSpace ℝ (Fin n))
    {γ : ℝ → M} (hγ : g.IsGeodesicOn γ (Icc (0 : ℝ) 1))
    (hγ0 : γ 0 = p)
    (hγv : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0) :
    g.globalExponential hc p v = γ 1 := by
  obtain ⟨hgeo, hzero, hvel⟩ := g.globalGeodesic_spec hc p v
  have hgeo' : g.IsGeodesicOn (g.globalGeodesic hc p v) (Icc (0 : ℝ) 1) :=
    fun t _ => hgeo t (mem_univ t)
  have heq := hgeo'.eq_nhds_on_of_initial_data hγ
    (convex_Icc (0 : ℝ) 1).isPreconnected (t₀ := 0) (by norm_num) p
    (by rw [hzero]; exact mem_extChartAt_source p)
    (hzero.trans hγ0.symm) (hvel.deriv.trans hγv.deriv.symm)
  exact (heq 1 (by norm_num)).self_of_nhds

/-- The complete exponential agrees near zero with a smooth exponential chart. -/
theorem exists_exponential_chart_eq_globalExponential_nhds
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M,
      (0 : EuclideanSpace ℝ (Fin n)) ∈ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v))
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) 0 ∧
      g.globalExponential hc p =ᶠ[𝓝 0] e := by
  exact g.exists_exponential_chart_eq_endpoint_nhds p (g.globalGeodesic hc p)
    (Eventually.of_forall fun v t _ => (g.globalGeodesic_spec hc p v).1 t (mem_univ t))
    (Eventually.of_forall fun v => (g.globalGeodesic_spec hc p v).2.1)
    (Eventually.of_forall fun v => (g.globalGeodesic_spec hc p v).2.2)

/-- A positive tangent-metric ball is an injectivity domain for the complete
exponential at every point. -/
theorem exists_pos_injOn_globalExponential (g : RiemannianMetric n M)
    (hc : MetricComplete g) (p : M) :
    ∃ r : ℝ, 0 < r ∧
      InjOn (g.globalExponential hc p) {v | g.tangentNorm p v < r} := by
  obtain ⟨e, he0, _, _, _, _, heq⟩ :=
    g.exists_exponential_chart_eq_globalExponential_nhds hc p
  obtain ⟨r, hr, hsub⟩ := g.exists_tangentBall_subset_nhds p
    (inter_mem (e.open_source.mem_nhds he0) heq)
  refine ⟨r, hr, ?_⟩
  intro v hv w hw h
  apply e.injOn (hsub hv).1 (hsub hw).1
  exact (hsub hv).2.symm.trans (h.trans (hsub hw).2)

/-- The supremum of the injective tangent-ball radii below the cutoff `C`. -/
noncomputable def truncatedInjectivityRadius (g : RiemannianMetric n M)
    (hc : MetricComplete g) (C : ℝ) (p : M) : ℝ :=
  sSup {r : ℝ | 0 ≤ r ∧ r ≤ C ∧
    InjOn (g.globalExponential hc p) {v | g.tangentNorm p v < r}}

theorem le_truncatedInjectivityRadius (g : RiemannianMetric n M)
    (hc : MetricComplete g) {C r : ℝ} (p : M) (hr : 0 ≤ r) (hrC : r ≤ C)
    (hinj : InjOn (g.globalExponential hc p) {v | g.tangentNorm p v < r}) :
    r ≤ g.truncatedInjectivityRadius hc C p :=
  le_csSup ⟨C, fun _ h => h.2.1⟩ ⟨hr, hrC, hinj⟩

theorem truncatedInjectivityRadius_nonneg (g : RiemannianMetric n M)
    (hc : MetricComplete g) {C : ℝ} (hC : 0 ≤ C) (p : M) :
    0 ≤ g.truncatedInjectivityRadius hc C p := by
  apply g.le_truncatedInjectivityRadius hc p le_rfl hC
  intro v hv
  exact False.elim ((not_lt_of_ge (Real.sqrt_nonneg _)) hv)

theorem truncatedInjectivityRadius_le (g : RiemannianMetric n M)
    (hc : MetricComplete g) {C : ℝ} (hC : 0 ≤ C) (p : M) :
    g.truncatedInjectivityRadius hc C p ≤ C := by
  apply csSup_le
  · refine ⟨0, le_rfl, hC, ?_⟩
    intro v hv
    exact False.elim ((not_lt_of_ge (Real.sqrt_nonneg _)) hv)
  · exact fun _ h => h.2.1

/-- The truncated radius is positive for every positive cutoff. -/
theorem truncatedInjectivityRadius_pos (g : RiemannianMetric n M)
    (hc : MetricComplete g) {C : ℝ} (hC : 0 < C) (p : M) :
    0 < g.truncatedInjectivityRadius hc C p := by
  obtain ⟨r, hr, hinj⟩ := g.exists_pos_injOn_globalExponential hc p
  have hpos : 0 < min r C := lt_min hr hC
  have hinj' : InjOn (g.globalExponential hc p)
      {v | g.tangentNorm p v < min r C} :=
    hinj.mono fun _ hv => hv.trans_le (min_le_left r C)
  exact hpos.trans_le
    (g.le_truncatedInjectivityRadius hc p hpos.le (min_le_right _ _) hinj')

/-- Every radius strictly below the truncated radius is an injectivity radius. -/
theorem injOn_globalExponential_of_lt_truncatedInjectivityRadius
    (g : RiemannianMetric n M) (hc : MetricComplete g) {C r : ℝ}
    (hC : 0 ≤ C) (p : M) (hr : r < g.truncatedInjectivityRadius hc C p) :
    InjOn (g.globalExponential hc p) {v | g.tangentNorm p v < r} := by
  have hne : ({s : ℝ | 0 ≤ s ∧ s ≤ C ∧
      InjOn (g.globalExponential hc p) {v | g.tangentNorm p v < s}}).Nonempty := by
    refine ⟨0, le_rfl, hC, ?_⟩
    intro v hv
    exact False.elim ((not_lt_of_ge (Real.sqrt_nonneg _)) hv)
  obtain ⟨s, hs, hrs⟩ := (lt_csSup_iff ⟨C, fun _ h => h.2.1⟩ hne).mp hr
  exact hs.2.2.mono fun _ hv => hv.trans hrs

/-- The open tangent ball at the supremal radius is itself an injectivity
domain; no assertion is made about its boundary. -/
theorem injOn_globalExponential_truncatedInjectivityRadius
    (g : RiemannianMetric n M) (hc : MetricComplete g) {C : ℝ}
    (hC : 0 ≤ C) (p : M) :
    InjOn (g.globalExponential hc p)
      {v | g.tangentNorm p v < g.truncatedInjectivityRadius hc C p} := by
  intro v hv w hw heq
  change g.tangentNorm p v < g.truncatedInjectivityRadius hc C p at hv
  change g.tangentNorm p w < g.truncatedInjectivityRadius hc C p at hw
  obtain ⟨r, hr, hrρ⟩ := exists_between (max_lt hv hw)
  exact g.injOn_globalExponential_of_lt_truncatedInjectivityRadius hc hC p hrρ
    ((le_max_left _ _).trans_lt hr) ((le_max_right _ _).trans_lt hr) heq

/-- A collision bounds the truncated radius by the larger initial speed. -/
theorem truncatedInjectivityRadius_le_max_of_collision
    (g : RiemannianMetric n M) (hc : MetricComplete g) {C : ℝ}
    (hC : 0 ≤ C) (p : M) {v w : EuclideanSpace ℝ (Fin n)}
    (hne : v ≠ w) (heq : g.globalExponential hc p v = g.globalExponential hc p w) :
    g.truncatedInjectivityRadius hc C p ≤ max (g.tangentNorm p v) (g.tangentNorm p w) := by
  by_contra h
  have hlt := lt_of_not_ge h
  exact hne (g.injOn_globalExponential_truncatedInjectivityRadius hc hC p
    ((le_max_left _ _).trans_lt hlt) ((le_max_right _ _).trans_lt hlt) heq)

/-- Injectivity fails above the truncated radius when still below the cutoff. -/
theorem not_injOn_globalExponential_of_truncatedInjectivityRadius_lt
    (g : RiemannianMetric n M) (hc : MetricComplete g) {C r : ℝ}
    (hC : 0 ≤ C) (p : M) (hr : g.truncatedInjectivityRadius hc C p < r)
    (hrC : r ≤ C) :
    ¬ InjOn (g.globalExponential hc p) {v | g.tangentNorm p v < r} := by
  intro hinj
  exact (not_le_of_gt hr) (g.le_truncatedInjectivityRadius hc p
    ((g.truncatedInjectivityRadius_nonneg hc hC p).trans hr.le) hrC hinj)

end PoincareMT.RiemannianMetric
