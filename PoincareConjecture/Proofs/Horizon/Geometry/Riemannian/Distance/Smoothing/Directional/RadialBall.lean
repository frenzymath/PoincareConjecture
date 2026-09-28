import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Smoothing.Directional.RadialPair

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology InnerProductSpace

theorem PoincareConjecture.RiemannianMetric.exists_distance_upper_support_of_opposite_pair_on_ball
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : PoincareConjecture.RiemannianMetric n M) (D : PoincareConjecture.LeviCivitaData g)
    (hc : PoincareConjecture.MetricComplete g) (p x : M) (hpx : p ≠ x)
    {U : Set M} (hU : IsOpen U) {f h : M → ℝ}
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f U)
    (hh : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ h U)
    (hball : ∀ y, g.edist p y ≤ g.edist p x → y ∈ U)
    {δ C : ℝ} (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hpair : ∀ y ∈ U,
      g.tangentNorm y (D.gradient f y) ≤ 1 ∧
      g.tangentNorm y (D.gradient h y) ≤ 1 ∧
      g.inner y (D.gradient f y) (D.gradient h y) ≤ -1 + 2 * δ)
    (hhess : ∀ y ∈ U, ∀ v : TangentSpace (𝓡 n) y,
      D.hessian f y v v ≤ C * g.inner y v v ∧
      D.hessian h y v v ≤ C * g.inner y v v) :
    ∃ (V : Set M) (rho : M → ℝ), IsOpen V ∧ x ∈ V ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho V ∧
      rho x = (g.edist p x).toReal ∧
      (∀ y ∈ V, (g.edist p y).toReal ≤ rho y) ∧
      g.inner x (D.gradient rho x) (D.gradient rho x) = 1 ∧
      |g.inner x (D.gradient rho x) (D.gradient f x)| ≤
        4 * Real.sqrt δ + |f x - f p| / (g.edist p x).toReal +
          C * (g.edist p x).toReal / 2 ∧
      |g.inner x (D.gradient rho x) (D.gradient h x)| ≤
        4 * Real.sqrt δ + |f x - f p| / (g.edist p x).toReal +
          C * (g.edist p x).toReal / 2 := by
  have hsum (y : M) (hy : y ∈ U) :
      g.tangentNorm y (D.gradient f y + D.gradient h y) ≤ 2 * Real.sqrt δ := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    obtain ⟨hfn, hhn, hfh⟩ := hpair y hy
    change ‖D.gradient f y‖ ≤ 1 at hfn
    change ‖D.gradient h y‖ ≤ 1 at hhn
    change ⟪D.gradient f y, D.gradient h y⟫_ℝ ≤ -1 + 2 * δ at hfh
    change ‖D.gradient f y + D.gradient h y‖ ≤ 2 * Real.sqrt δ
    have hf2 : ‖D.gradient f y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (D.gradient f y)]
    have hh2 : ‖D.gradient h y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (D.gradient h y)]
    have heq := norm_add_sq_real (D.gradient f y) (D.gradient h y)
    nlinarith [Real.sq_sqrt hδ, Real.sqrt_nonneg δ,
      norm_nonneg (D.gradient f y + D.gradient h y)]
  obtain ⟨ε, hε, γ, hγ, hγ0, hγ1, hmin⟩ :=
    g.exists_minimizing_geodesic_of_metricComplete hc p x
  have hγclosed : g.IsGeodesicOn γ (Icc 0 1) := by
    intro t ht
    apply hγ t
    constructor <;> linarith [ht.1, ht.2]
  have hmin' : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist (γ 0) (γ 1) := by
    simpa only [hγ0, hγ1] using hmin
  have hγU : MapsTo γ (Icc (0 : ℝ) 1) U := by
    intro t ht
    apply hball
    have hm := hmin 0 (by simp) t ht
    simp only [hγ0, zero_sub, abs_neg, abs_of_nonneg ht.1] at hm
    rw [hm]
    exact mul_le_of_le_one_left' (by exact_mod_cast ht.2)
  obtain ⟨V, rho, hV, hxV, hrho, hvalue, hupper, _, hunit, hfbound, hhbound⟩ :=
    g.exists_distance_upper_support_gradient_pair_abs_le_with_gap D hc hγclosed
      (by simpa only [hγ0, hγ1] using hpx) hmin' hU hf hh hγU
      (by positivity : 0 ≤ 2 * Real.sqrt δ) hC
      (fun t ht => hsum (γ t) (hγU ht))
      (fun t ht v => (hhess (γ t) (hγU ht) v).1)
      (fun t ht v => (hhess (γ t) (hγU ht) v).2)
  simp only [hγ0, hγ1] at hxV hvalue hupper hunit hfbound hhbound
  refine ⟨V, rho, hV, hxV, hrho, hvalue, hupper, hγ1 ▸ hunit, ?_, ?_⟩
  · convert (hγ1 ▸ hfbound) using 1; ring
  · convert (hγ1 ▸ hhbound) using 1; ring

theorem PoincareConjecture.RiemannianMetric.exists_distance_upper_support_of_opposite_pairs_on_ball
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : PoincareConjecture.RiemannianMetric n M) (D : PoincareConjecture.LeviCivitaData g)
    (hc : PoincareConjecture.MetricComplete g) (p x : M) (hpx : p ≠ x)
    {U : Set M} (hU : IsOpen U) {ι : Type*} {f h : ι → M → ℝ}
    (hf : ∀ i, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f i) U)
    (hh : ∀ i, ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (h i) U)
    (hball : ∀ y, g.edist p y ≤ g.edist p x → y ∈ U)
    {δ C : ℝ} (hδ : 0 ≤ δ) (hC : 0 ≤ C)
    (hpair : ∀ i y, y ∈ U →
      g.tangentNorm y (D.gradient (f i) y) ≤ 1 ∧
      g.tangentNorm y (D.gradient (h i) y) ≤ 1 ∧
      g.inner y (D.gradient (f i) y) (D.gradient (h i) y) ≤ -1 + 2 * δ)
    (hhess : ∀ i y, y ∈ U → ∀ v : TangentSpace (𝓡 n) y,
      D.hessian (f i) y v v ≤ C * g.inner y v v ∧
      D.hessian (h i) y v v ≤ C * g.inner y v v) :
    ∃ (V : Set M) (rho : M → ℝ), IsOpen V ∧ x ∈ V ∧
      ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ rho V ∧
      rho x = (g.edist p x).toReal ∧
      (∀ y ∈ V, (g.edist p y).toReal ≤ rho y) ∧
      g.inner x (D.gradient rho x) (D.gradient rho x) = 1 ∧
      ∀ i, |g.inner x (D.gradient rho x) (D.gradient (f i) x)| ≤
        4 * Real.sqrt δ + |f i x - f i p| / (g.edist p x).toReal +
          C * (g.edist p x).toReal / 2 ∧
      |g.inner x (D.gradient rho x) (D.gradient (h i) x)| ≤
        4 * Real.sqrt δ + |f i x - f i p| / (g.edist p x).toReal +
          C * (g.edist p x).toReal / 2 := by
  have hsum (i : ι) (y : M) (hy : y ∈ U) :
      g.tangentNorm y (D.gradient (f i) y + D.gradient (h i) y) ≤ 2 * Real.sqrt δ := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    obtain ⟨hfn, hhn, hfh⟩ := hpair i y hy
    change ‖D.gradient (f i) y‖ ≤ 1 at hfn
    change ‖D.gradient (h i) y‖ ≤ 1 at hhn
    change ⟪D.gradient (f i) y, D.gradient (h i) y⟫_ℝ ≤ -1 + 2 * δ at hfh
    change ‖D.gradient (f i) y + D.gradient (h i) y‖ ≤ 2 * Real.sqrt δ
    have hf2 : ‖D.gradient (f i) y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (D.gradient (f i) y)]
    have hh2 : ‖D.gradient (h i) y‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (D.gradient (h i) y)]
    have heq := norm_add_sq_real (D.gradient (f i) y) (D.gradient (h i) y)
    nlinarith [Real.sq_sqrt hδ, Real.sqrt_nonneg δ,
      norm_nonneg (D.gradient (f i) y + D.gradient (h i) y)]
  obtain ⟨ε, hε, γ, hγ, hγ0, hγ1, hmin⟩ :=
    g.exists_minimizing_geodesic_of_metricComplete hc p x
  have hγclosed : g.IsGeodesicOn γ (Icc 0 1) := by
    intro t ht
    apply hγ t
    constructor <;> linarith [ht.1, ht.2]
  have hmin' : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      g.edist (γ s) (γ t) = ENNReal.ofReal |s - t| * g.edist (γ 0) (γ 1) := by
    simpa only [hγ0, hγ1] using hmin
  have hγU : MapsTo γ (Icc (0 : ℝ) 1) U := by
    intro t ht
    apply hball
    have hm := hmin 0 (by simp) t ht
    simp only [hγ0, zero_sub, abs_neg, abs_of_nonneg ht.1] at hm
    rw [hm]
    exact mul_le_of_le_one_left' (by exact_mod_cast ht.2)
  obtain ⟨V, rho, hV, hxV, hrho, hvalue, hupper, hgrad, hunit⟩ :=
    g.exists_distance_radial_upper_support_on_minimizing_segment D hc hγclosed
      (by simpa only [hγ0, hγ1] using hpx) hmin'
  have hbounds (i : ι) :
      |g.inner (γ 1) (D.gradient rho (γ 1)) (D.gradient (f i) (γ 1))| ≤
        4 * Real.sqrt δ + |f i (γ 1) - f i (γ 0)| /
          (g.edist (γ 0) (γ 1)).toReal +
          C * (g.edist (γ 0) (γ 1)).toReal / 2 ∧
      |g.inner (γ 1) (D.gradient rho (γ 1)) (D.gradient (h i) (γ 1))| ≤
        4 * Real.sqrt δ + |f i (γ 1) - f i (γ 0)| /
          (g.edist (γ 0) (γ 1)).toReal +
          C * (g.edist (γ 0) (γ 1)).toReal / 2 := by
    obtain ⟨_, other, _, _, _, _, _, hother, _, hfbound, hhbound⟩ :=
      g.exists_distance_upper_support_gradient_pair_abs_le_with_gap D hc hγclosed
        (by simpa only [hγ0, hγ1] using hpx) hmin' hU (hf i) (hh i) hγU
        (by positivity : 0 ≤ 2 * Real.sqrt δ) hC
        (fun t ht => hsum i (γ t) (hγU ht))
        (fun t ht v => (hhess i (γ t) (hγU ht) v).1)
        (fun t ht v => (hhess i (γ t) (hγU ht) v).2)
    have heq : D.gradient rho (γ 1) = D.gradient other (γ 1) := hgrad.trans hother.symm
    rw [heq]
    constructor
    · convert hfbound using 1; ring
    · convert hhbound using 1; ring
  simp only [hγ0, hγ1] at hxV hvalue hupper
  refine ⟨V, rho, hV, hxV, hrho, hvalue, hupper, hγ1 ▸ hunit, ?_⟩
  intro i
  have hb := hbounds i
  simp only [hγ0] at hb
  exact hγ1 ▸ hb
