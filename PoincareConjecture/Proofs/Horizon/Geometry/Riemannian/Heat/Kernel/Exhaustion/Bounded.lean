import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Bounds








set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Topology Bundle ENNReal

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M] {g : RiemannianMetric n M}


theorem exists_dirichletHeatKernel_exhaustion_local_bound
    (D : LeviCivitaData g) (hn : 0 < n) (hc : MetricComplete g)
    {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (hΩ : ∀ j, IsOpen (Ω j)) (hΩmono : Monotone Ω)
    (hcover : (⋃ j, Ω j) = univ) {K : ℕ → ℝ → M → M → ℝ}
    (hK : ∀ j, Dirichlet.IsDirichletHeatKernel D (Ω j) (K j))
    (hmono : ∀ t, 0 < t → ∀ x y, Monotone (fun j => K j t x y))
    (O : M) {R : ℝ} (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ j t, 0 < t → ∀ x, (g.edist O x).toReal ≤ R → ∀ y,
      K j t x y ≤ Real.exp (2 * (n : ℝ) * Real.log 2 + C * t +
        (2 * R) ^ 2 / (2 * t)) / g.volumeMeasure.real (g.ball O 1) := by
  obtain ⟨C, hC, hbound⟩ :=
    D.exists_dirichletHeatKernel_bound_on_domains_containing_ball hn hc hk hRic O hR
  have hcball := g.isCompact_closedBall_of_metricComplete hc O (15 * R)
  obtain ⟨N, hN⟩ := hcball.elim_directed_cover Ω hΩ (by rw [hcover]; exact subset_univ _)
      (fun i j => ⟨max i j, hΩmono (le_max_left _ _), hΩmono (le_max_right _ _)⟩)
  have hcontains : {z | (g.edist O z).toReal ≤ 15 * R} ⊆ Ω N := by
    intro z hz
    apply hN
    change g.edist O z ≤ ENNReal.ofReal (15 * R)
    calc
      g.edist O z = ENNReal.ofReal (g.edist O z).toReal :=
        (ENNReal.ofReal_toReal (g.edist_ne_top O z)).symm
      _ ≤ ENNReal.ofReal (15 * R) := ENNReal.ofReal_le_ofReal hz
  refine ⟨C, hC, ?_⟩
  intro j t ht x hx y
  exact (hmono t ht x y (le_max_left j N)).trans
    (hbound (Ω (max j N)) (hΩ _) (hcontains.trans (hΩmono (le_max_right j N)))
      (K (max j N)) (hK _) t ht x hx y)


theorem bddAbove_dirichletHeatKernel_exhaustion
    (D : LeviCivitaData g) (hn : 0 < n) (hc : MetricComplete g)
    {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (hΩ : ∀ j, IsOpen (Ω j)) (hΩmono : Monotone Ω)
    (hcover : (⋃ j, Ω j) = univ) {K : ℕ → ℝ → M → M → ℝ}
    (hK : ∀ j, Dirichlet.IsDirichletHeatKernel D (Ω j) (K j))
    (hmono : ∀ t, 0 < t → ∀ x y, Monotone (fun j => K j t x y))
    {t : ℝ} (ht : 0 < t) (x y : M) :
    BddAbove (range (fun j => K j t x y)) := by
  obtain ⟨C, _, hbound⟩ := D.exists_dirichletHeatKernel_exhaustion_local_bound
    hn hc hk hRic hΩ hΩmono hcover hK hmono x (R := 1) le_rfl
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hx : (g.edist x x).toReal ≤ 1 := by
    simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self, ENNReal.toReal_zero]
    norm_num
  refine ⟨Real.exp (2 * (n : ℝ) * Real.log 2 + C * t + (2 * 1) ^ 2 / (2 * t)) /
    g.volumeMeasure.real (g.ball x 1), ?_⟩
  rintro _ ⟨j, rfl⟩
  exact hbound j t ht x hx y



theorem exists_dirichletHeatKernel_exhaustion_compact_time_bound
    (D : LeviCivitaData g) (hn : 0 < n) (hc : MetricComplete g)
    {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (hΩ : ∀ j, IsOpen (Ω j)) (hΩmono : Monotone Ω)
    (hcover : (⋃ j, Ω j) = univ) {K : ℕ → ℝ → M → M → ℝ}
    (hK : ∀ j, Dirichlet.IsDirichletHeatKernel D (Ω j) (K j))
    (hmono : ∀ t, 0 < t → ∀ x y, Monotone (fun j => K j t x y))
    (O : M) {R : ℝ} (hR : 1 ≤ R) {a b : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 < B ∧ ∀ j t, t ∈ Icc a b →
      ∀ x, (g.edist O x).toReal ≤ R → ∀ y, K j t x y ≤ B := by
  obtain ⟨C, hC, hbound⟩ := D.exists_dirichletHeatKernel_exhaustion_local_bound
    hn hc hk hRic hΩ hΩmono hcover hK hmono O hR
  have hvol : 0 < g.volumeMeasure.real (g.ball O 1) :=
    ENNReal.toReal_pos (g.volumeMeasure_ball_pos O zero_lt_one).ne'
      (g.volumeMeasure_ball_lt_top hc O 1).ne
  refine ⟨Real.exp (2 * (n : ℝ) * Real.log 2 + C * b + (2 * R) ^ 2 / (2 * a)) /
    g.volumeMeasure.real (g.ball O 1), div_pos (Real.exp_pos _) hvol, ?_⟩
  intro j t ht x hx y
  have htpos : 0 < t := ha.trans_le ht.1
  apply (hbound j t htpos x hx y).trans
  apply div_le_div_of_nonneg_right ?_ hvol.le
  apply Real.exp_le_exp.mpr
  gcongr
  · exact ht.2
  · exact ht.1

end PoincareConjecture.LeviCivitaData
