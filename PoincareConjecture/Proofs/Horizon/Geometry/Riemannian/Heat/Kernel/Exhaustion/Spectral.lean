import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Dirichlet
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Bounded

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.LeviCivitaData

theorem monotone_heatKernelContinuousTime_exhaustion
    {n : ℕ} [NeZero n] {M : Type u} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {Ω : ℕ → Set M} (S : ∀ j, Poincare.Manifold.SmoothDomain n (Ω j))
    (hΩmono : Monotone Ω) {t : ℝ} (ht : 0 < t) (x y : M) :
    Monotone (fun j => Dirichlet.heatKernelContinuousTime D (S j) t x y) := by
  intro i j hij
  change Dirichlet.heatKernelContinuousTime D (S i) t x y ≤
    Dirichlet.heatKernelContinuousTime D (S j) t x y
  have hKi := Dirichlet.heatKernelContinuousTime_isDirichletHeatKernel D (S i)
  have hKj := Dirichlet.heatKernelContinuousTime_isDirichletHeatKernel D (S j)
  by_cases hx : x ∈ Ω i
  · by_cases hy : y ∈ Ω i
    · simp only [Dirichlet.heatKernelContinuousTime_of_pos D (S i) ht,
        Dirichlet.heatKernelContinuousTime_of_pos D (S j) ht]
      exact Dirichlet.heatKernelContinuous_domain_mono D (S i) (S j)
        (hΩmono hij) t ht x y hx hy
    · rw [hKi.zero_outside t ht x y (Or.inr hy)]
      exact hKj.nonneg t ht x y
  · rw [hKi.zero_outside t ht x y (Or.inl hx)]
    exact hKj.nonneg t ht x y

theorem exists_canonical_dirichletHeatKernel_exhaustion
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    [PreconnectedSpace M] [NoncompactSpace M]
    {g : RiemannianMetric (n + 1) M} (D : LeviCivitaData g) :
    ∃ (Ω : ℕ → Set M) (S : ∀ j, Poincare.Manifold.SmoothDomain (n + 1) (Ω j)),
      (∀ j, closure (Ω j) ⊆ Ω (j + 1)) ∧ (⋃ j, Ω j) = univ ∧
      (∀ j, Dirichlet.IsDirichletHeatKernel D (Ω j)
        (Dirichlet.heatKernelContinuousTime D (S j))) ∧
      (∀ t, 0 < t → ∀ x y,
        Monotone (fun j => Dirichlet.heatKernelContinuousTime D (S j) t x y)) := by
  classical
  let : SecondCountableTopology M := g.secondCountableTopology
  obtain ⟨Ω, hΩ, hnest, hcover⟩ :=
    Poincare.Manifold.exists_smoothDomain_exhaustion (n := n) (M := M)
  let S := fun j => (hΩ j).some
  refine ⟨Ω, S, hnest, hcover,
    fun j => Dirichlet.heatKernelContinuousTime_isDirichletHeatKernel D (S j), ?_⟩
  have hΩmono : Monotone Ω := monotone_nat_of_le_succ fun j =>
    subset_closure.trans (hnest j)
  exact fun _ ht x y => D.monotone_heatKernelContinuousTime_exhaustion S hΩmono ht x y

section Bounds

variable {n : ℕ} [NeZero n] {M : Type u} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M] {g : RiemannianMetric n M}

theorem exists_heatKernelContinuousTime_exhaustion_local_bound
    (D : LeviCivitaData g) (hn : 0 < n) (hc : MetricComplete g)
    {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ j, Poincare.Manifold.SmoothDomain n (Ω j))
    (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ)
    (O : M) {R : ℝ} (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ j t, 0 < t → ∀ x, (g.edist O x).toReal ≤ R → ∀ y,
      Dirichlet.heatKernelContinuousTime D (S j) t x y ≤
        Real.exp (2 * (n : ℝ) * Real.log 2 + C * t + (2 * R) ^ 2 / (2 * t)) /
          g.volumeMeasure.real (g.ball O 1) :=
  D.exists_dirichletHeatKernel_exhaustion_local_bound hn hc hk hRic
    (fun j => (S j).isOpen) hΩmono hcover
    (fun j => Dirichlet.heatKernelContinuousTime_isDirichletHeatKernel D (S j))
    (fun _ ht x y => D.monotone_heatKernelContinuousTime_exhaustion S hΩmono ht x y)
    O hR

theorem bddAbove_heatKernelContinuousTime_exhaustion
    (D : LeviCivitaData g) (hn : 0 < n) (hc : MetricComplete g)
    {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ j, Poincare.Manifold.SmoothDomain n (Ω j))
    (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ)
    {t : ℝ} (ht : 0 < t) (x y : M) :
    BddAbove (range (fun j => Dirichlet.heatKernelContinuousTime D (S j) t x y)) :=
  D.bddAbove_dirichletHeatKernel_exhaustion hn hc hk hRic
    (fun j => (S j).isOpen) hΩmono hcover
    (fun j => Dirichlet.heatKernelContinuousTime_isDirichletHeatKernel D (S j))
    (fun _ ht x y => D.monotone_heatKernelContinuousTime_exhaustion S hΩmono ht x y)
    ht x y

theorem exists_heatKernelContinuousTime_exhaustion_compact_time_bound
    (D : LeviCivitaData g) (hn : 0 < n) (hc : MetricComplete g)
    {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ j, Poincare.Manifold.SmoothDomain n (Ω j))
    (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ)
    (O : M) {R : ℝ} (hR : 1 ≤ R) {a b : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 < B ∧ ∀ j t, t ∈ Icc a b →
      ∀ x, (g.edist O x).toReal ≤ R → ∀ y,
        Dirichlet.heatKernelContinuousTime D (S j) t x y ≤ B :=
  D.exists_dirichletHeatKernel_exhaustion_compact_time_bound hn hc hk hRic
    (fun j => (S j).isOpen) hΩmono hcover
    (fun j => Dirichlet.heatKernelContinuousTime_isDirichletHeatKernel D (S j))
    (fun _ ht x y => D.monotone_heatKernelContinuousTime_exhaustion S hΩmono ht x y)
    O hR ha

open Poincare.Analysis.Dirichlet.Kernel

theorem exists_evaluationRow_exhaustion_compact_time_bound
    (D : LeviCivitaData g) (hn : 0 < n) (hc : MetricComplete g)
    {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 n) x), -k * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ j, Poincare.Manifold.SmoothDomain n (Ω j))
    (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ)
    (O : M) {R : ℝ} (hR : 1 ≤ R) {a b : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 < B ∧ ∀ j t (ht : t ∈ Icc a b),
      ∀ x, (g.edist O x).toReal ≤ R →
        ‖evaluationRow (Dirichlet.Boundary.heatPowerContinuous D (S j) 0 t
          (ha.trans_le ht.1)) x‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ :=
    D.exists_heatKernelContinuousTime_exhaustion_compact_time_bound hn hc hk hRic
      S hΩmono hcover O hR (a := a + a) (b := b + b) (add_pos ha ha)
  refine ⟨Real.sqrt B, Real.sqrt_pos.mpr hB, ?_⟩
  intro j t ht x hx
  have htpos := ha.trans_le ht.1
  have hdiag := hbound j (t + t) ⟨add_le_add ht.1 ht.1, add_le_add ht.2 ht.2⟩ x hx x
  rw [Dirichlet.heatKernelContinuousTime_of_pos D (S j) (add_pos htpos htpos),
    Dirichlet.heatKernelContinuous_add_eq_inner D (S j) t t htpos htpos,
    real_inner_self_eq_norm_sq] at hdiag
  exact Real.le_sqrt_of_sq_le hdiag

end Bounds

end PoincareConjecture.LeviCivitaData
