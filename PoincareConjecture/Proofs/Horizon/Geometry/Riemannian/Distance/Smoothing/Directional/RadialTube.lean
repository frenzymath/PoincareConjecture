import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.RadialBall







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Manifold ContDiff Bundle Topology

theorem PoincareConjecture.RiemannianMetric.eventually_radial_pair_bound_of_gap_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : PoincareConjecture.RiemannianMetric n M) {ι : Type*} [Finite ι]
    {f : ι → M → ℝ} {p x : M} (hpx : p ≠ x)
    (hf : ∀ i, ContinuousAt (f i) x) {q : ℝ}
    (hgap : ∀ i, |f i x - f i p| / (g.edist p x).toReal ≤ q)
    (δ C : ℝ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ y in 𝓝 x, p ≠ y ∧ ∀ i,
      4 * Real.sqrt δ + |f i y - f i p| / (g.edist p y).toReal +
        C * (g.edist p y).toReal / 2 <
      4 * Real.sqrt δ + q + C * (g.edist p x).toReal / 2 + η := by
  let := g.toMetricSpace
  have hd : ContinuousAt (fun y => (g.edist p y).toReal) x :=
    (g.continuous_toReal_edist p).continuousAt
  have hdx : (g.edist p x).toReal ≠ 0 := (dist_pos.mpr hpx).ne'
  have hb (i : ι) : ∀ᶠ y in 𝓝 x,
      4 * Real.sqrt δ + |f i y - f i p| / (g.edist p y).toReal +
        C * (g.edist p y).toReal / 2 <
      4 * Real.sqrt δ + q + C * (g.edist p x).toReal / 2 + η := by
    have hc : ContinuousAt (fun y =>
        4 * Real.sqrt δ + |f i y - f i p| / (g.edist p y).toReal +
          C * (g.edist p y).toReal / 2) x :=
      (continuousAt_const.add (((hf i).sub continuousAt_const).abs.div hd hdx)).add
        ((continuousAt_const.mul hd).div_const 2)
    apply hc.eventually_lt continuousAt_const
    linarith [hgap i]
  filter_upwards [isOpen_compl_singleton.mem_nhds (show x ∉ ({p} : Set M) by
    simpa only [mem_singleton_iff] using hpx.symm),
    eventually_all.mpr hb] with y hy hb
  exact ⟨(show y ≠ p from hy).symm, hb⟩



theorem PoincareConjecture.RiemannianMetric.exists_radial_support_neighborhood_of_gap_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : PoincareConjecture.RiemannianMetric n M) (D : PoincareConjecture.LeviCivitaData g)
    (hc : PoincareConjecture.MetricComplete g) {ι : Type*} [Finite ι]
    {f h : ι → M → ℝ} {p x : M} (hpx : p ≠ x)
    {U : Set M} (hU : IsOpen U)
    (hf : ∀ i, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i) U)
    (hh : ∀ i, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (h i) U)
    {R : ℝ} (hRx : (g.edist p x).toReal < R)
    (hball : ∀ y, g.edist p y ≤ ENNReal.ofReal R → y ∈ U)
    {δ C : ℝ} (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hpair : ∀ i y, y ∈ U →
      g.tangentNorm y (D.gradient (f i) y) ≤ 1 ∧
      g.tangentNorm y (D.gradient (h i) y) ≤ 1 ∧
      g.inner y (D.gradient (f i) y) (D.gradient (h i) y) ≤ -1 + 2 * δ)
    (hhess : ∀ i y, y ∈ U → ∀ v : TangentSpace (𝓡 n) y,
      D.hessian (f i) y v v ≤ C * g.inner y v v ∧
      D.hessian (h i) y v v ≤ C * g.inner y v v)
     {q : ℝ} (hgap : ∀ i, |f i x - f i p| / (g.edist p x).toReal ≤ q)
    {η : ℝ} (hη : 0 < η) :
    ∃ W : Set M, IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧
      ∀ y ∈ W, p ≠ y ∧
        ∃ (V : Set M) (rho : M → ℝ), IsOpen V ∧ y ∈ V ∧
          ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho V ∧
          rho y = (g.edist p y).toReal ∧
          (∀ z ∈ V, (g.edist p z).toReal ≤ rho z) ∧
          g.inner y (D.gradient rho y) (D.gradient rho y) = 1 ∧
          ∀ i, |g.inner y (D.gradient rho y) (D.gradient (f i) y)| ≤
            4 * Real.sqrt δ + q + C * (g.edist p x).toReal / 2 + η ∧
          |g.inner y (D.gradient rho y) (D.gradient (h i) y)| ≤
            4 * Real.sqrt δ + q + C * (g.edist p x).toReal / 2 + η := by
  have hrad (y : M) (hy : (g.edist p y).toReal < R) :
      g.edist p y ≤ ENNReal.ofReal R := by
    rw [← ENNReal.ofReal_toReal (g.edist_ne_top p y)]
    exact ENNReal.ofReal_le_ofReal hy.le
  have hxU := hball x (hrad x hRx)
  have hev := g.eventually_radial_pair_bound_of_gap_bound hpx
    (fun i => ((hf i).contMDiffAt (hU.mem_nhds hxU)).continuousAt) hgap δ C hη
  have hev' : ∀ᶠ y in 𝓝 x, (g.edist p y).toReal < R ∧ p ≠ y ∧ ∀ i,
      4 * Real.sqrt δ + |f i y - f i p| / (g.edist p y).toReal +
        C * (g.edist p y).toReal / 2 <
      4 * Real.sqrt δ + q + C * (g.edist p x).toReal / 2 + η := by
    filter_upwards [hev, (g.continuous_toReal_edist p).continuousAt.eventually_lt
      continuousAt_const hRx] with y hy hdist
    exact ⟨hdist, hy⟩
  obtain ⟨W, hWsub, hW, hxW⟩ := mem_nhds_iff.mp hev'
  refine ⟨W, hW, hxW, fun y hy => hball y (hrad y (hWsub hy).1), ?_⟩
  intro y hy
  obtain ⟨hyR, hpy, hb⟩ := hWsub hy
  refine ⟨hpy, ?_⟩
  obtain ⟨V, rho, hV, hyV, hrho, hvalue, hupper, hunit, hbounds⟩ :=
    g.exists_distance_upper_support_of_opposite_pairs_on_ball D hc p y hpy hU hf hh
      (fun z hz => hball z (hz.trans (hrad y hyR))) hδ hC hpair hhess
  exact ⟨V, rho, hV, hyV, hrho, hvalue, hupper, hunit,
    fun i => ⟨(hbounds i).1.trans (hb i).le, (hbounds i).2.trans (hb i).le⟩⟩
