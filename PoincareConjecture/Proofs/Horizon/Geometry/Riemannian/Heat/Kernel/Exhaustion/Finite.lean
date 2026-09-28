import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Bounded
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Supremum
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Initial

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  [PreconnectedSpace M] [NoncompactSpace M]
  {g : RiemannianMetric (n + 1) M}

theorem exists_bounded_dirichletHeatKernel_exhaustion
    (D : LeviCivitaData g) (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 (n + 1)) x),
      -k * g.inner x v v ≤ D.ricci x v v) :
    ∃ (Ω : ℕ → Set M) (_S : ∀ j, Poincare.Manifold.SmoothDomain (n + 1) (Ω j))
      (K : ℕ → ℝ → M → M → ℝ),
      (∀ j, closure (Ω j) ⊆ Ω (j + 1)) ∧ (⋃ j, Ω j) = univ ∧
      (∀ j, Dirichlet.IsDirichletHeatKernel D (Ω j) (K j)) ∧
      (∀ t, 0 < t → ∀ x y, Monotone (fun j => K j t x y)) ∧
      (∀ t, 0 < t → ∀ x y, BddAbove (range (fun j => K j t x y))) := by
  obtain ⟨Ω, S, K, hnest, hcover, hK, hmono⟩ := D.exists_dirichletHeatKernel_exhaustion
  have hΩmono : Monotone Ω := monotone_nat_of_le_succ fun j =>
    subset_closure.trans (hnest j)
  exact ⟨Ω, S, K, hnest, hcover, hK, hmono, fun _ ht x y =>
    D.bddAbove_dirichletHeatKernel_exhaustion (Nat.succ_pos _) hc hk hRic
      (fun j => (S j).isOpen) hΩmono hcover hK hmono ht x y⟩

theorem exists_positive_subprobability_kernel
    (D : LeviCivitaData g) (hc : MetricComplete g) {k : ℝ} (hk : 0 ≤ k)
    (hRic : ∀ x (v : TangentSpace (𝓡 (n + 1)) x),
      -k * g.inner x v v ≤ D.ricci x v v) :
    ∃ H : ℝ → M → M → ℝ,
      (∀ t, 0 < t → ∀ x y, 0 < H t x y) ∧
      (∀ t, 0 < t → ∀ x y, H t x y = H t y x) ∧
      LowerSemicontinuous (fun p : (M × M) × Ioi (0 : ℝ) => H p.2 p.1.1 p.1.2) ∧
      (∀ t, 0 < t → ∀ x, Integrable (H t x) g.volumeMeasure ∧
        (∫ y, H t x y ∂g.volumeMeasure) ≤ 1) ∧
      (∀ s t, 0 < s → 0 < t → ∀ x y,
        Integrable (fun z => H s x z * H t z y) g.volumeMeasure ∧
          H (s + t) x y = ∫ z, H s x z * H t z y ∂g.volumeMeasure) ∧
      (∀ φ : M → ℝ, Continuous φ → HasCompactSupport φ → ∀ x,
        Tendsto (fun t => ∫ y, H t x y * φ y ∂g.volumeMeasure)
          (𝓝[>] 0) (𝓝 (φ x))) ∧
      (∀ O : M, ∀ R : ℝ, 1 ≤ R → ∀ a b : ℝ, 0 < a →
        ∃ B : ℝ, 0 < B ∧ ∀ t ∈ Icc a b, ∀ x,
          (g.edist O x).toReal ≤ R → ∀ y, H t x y ≤ B) := by
  obtain ⟨Ω, S, K, hnest, hcover, hK, hmono, hbdd⟩ :=
    D.exists_bounded_dirichletHeatKernel_exhaustion hc hk hRic
  have hΩmono : Monotone Ω := monotone_nat_of_le_succ fun j =>
    subset_closure.trans (hnest j)
  refine ⟨dirichletExhaustionKernel K,
    fun _ ht x y => DirichletExhaustion.positive hK hbdd hΩmono hcover ht x y,
    fun _ ht x y => DirichletExhaustion.symmetric hK ht x y,
    DirichletExhaustion.lowerSemicontinuous hK hbdd,
    fun _ ht x => DirichletExhaustion.mass hK hmono hbdd ht x,
    fun _ _ hs ht x y => DirichletExhaustion.semigroup hK hmono hbdd hs ht x y,
    fun φ hφ hφc x => tendsto_integral_iSup_dirichletHeatKernel_initial
      hK hcover hmono hbdd hφ hφc x, ?_⟩
  intro O R hR a b ha
  obtain ⟨B, hB, hbound⟩ := D.exists_dirichletHeatKernel_exhaustion_compact_time_bound
    (Nat.succ_pos _) hc hk hRic (fun j => (S j).isOpen) hΩmono hcover hK hmono
    O hR (b := b) ha
  exact ⟨B, hB, fun t ht x hx y => ciSup_le (fun j => hbound j t ht x hx y)⟩

end PoincareConjecture.LeviCivitaData
