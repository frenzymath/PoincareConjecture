import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Finite
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Spectral
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Minimal









set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.LeviCivitaData



theorem exists_positive_subprobability_kernel_le_fundamental_solutions
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
    [IsManifold (𝓡 (n + 1)) ∞ M]
    [PreconnectedSpace M] [NoncompactSpace M]
    {g : RiemannianMetric (n + 1) M}
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
          (g.edist O x).toReal ≤ R → ∀ y, H t x y ≤ B) ∧
      (∀ (u : M → ℝ → ℝ) (y : M),
        ContinuousOn (Function.uncurry u) (univ ×ˢ Ioi 0) →
        (∀ t, 0 < t → ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ (fun x => u x t)) →
        (∀ x t, 0 < t → HasDerivAt (u x) (D.laplacian (fun z => u z t) x) t) →
        (∀ x t, 0 < t → 0 ≤ u x t) →
        (∀ φ : M → ℝ, Continuous φ → HasCompactSupport φ →
          Tendsto (fun t => ∫ z, φ z * u z t ∂g.volumeMeasure)
            (𝓝[>] 0) (𝓝 (φ y))) →
        ∀ x t, 0 < t → H t x y ≤ u x t) := by
  obtain ⟨Ω, S, hnest, hcover, hK, hmono⟩ :=
    D.exists_canonical_dirichletHeatKernel_exhaustion
  let K := fun j => Dirichlet.heatKernelContinuousTime D (S j)
  have hΩmono : Monotone Ω := monotone_nat_of_le_succ fun j =>
    subset_closure.trans (hnest j)
  have hbdd (t : ℝ) (ht : 0 < t) (x y : M) : BddAbove (range (fun j => K j t x y)) :=
    D.bddAbove_heatKernelContinuousTime_exhaustion (Nat.succ_pos _) hc hk hRic
      S hΩmono hcover ht x y
  refine ⟨dirichletExhaustionKernel K,
    fun _ ht x y => DirichletExhaustion.positive hK hbdd hΩmono hcover ht x y,
    fun _ ht x y => DirichletExhaustion.symmetric hK ht x y,
    DirichletExhaustion.lowerSemicontinuous hK hbdd,
    fun _ ht x => DirichletExhaustion.mass hK hmono hbdd ht x,
    fun _ _ hs ht x y => DirichletExhaustion.semigroup hK hmono hbdd hs ht x y,
    fun φ hφ hφc x => tendsto_integral_iSup_dirichletHeatKernel_initial
      hK hcover hmono hbdd hφ hφc x, ?_, ?_⟩
  · intro O R hR a b ha
    obtain ⟨B, hB, hbound⟩ := D.exists_heatKernelContinuousTime_exhaustion_compact_time_bound
      (Nat.succ_pos _) hc hk hRic S hΩmono hcover O hR (b := b) ha
    exact ⟨B, hB, fun t ht x hx y => ciSup_le (fun j => hbound j t ht x hx y)⟩
  · intro u y hcont hspace hheat hnonneg htrace x t ht
    exact D.dirichletExhaustionKernel_le_of_nonnegative_heat_solution S
      hcont hspace hheat hnonneg htrace ht x

end PoincareConjecture.LeviCivitaData
