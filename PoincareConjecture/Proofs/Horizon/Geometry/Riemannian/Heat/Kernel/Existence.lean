import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.LineMinimal
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Equation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.AllTimeMoment
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Conservation.Exhaustion

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.RiemannianMetric

open LeviCivitaData

theorem exists_minimal_smooth_conservativeHeatKernel
    (n : ℕ) (K : ℝ) (hn : 0 < n) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M]
        [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
        [IsManifold (𝓡 n) ∞ M] [PreconnectedSpace M] [NoncompactSpace M]
        (g : RiemannianMetric n M), MetricComplete g →
        ∀ D : LeviCivitaData g,
          (∀ x v w, |D.sectionalCurvature x v w| ≤ K) →
          ∃ H : M → M → ℝ → ℝ,
            (∀ x y t, 0 < t → 0 < H x y t) ∧
            ContMDiffOn ((𝓘(ℝ, ℝ).prod (𝓡 n)).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
              (fun p : (ℝ × M) × M => H p.1.2 p.2 p.1.1)
              ((Ioi 0 ×ˢ univ) ×ˢ univ) ∧
            (∀ x y t, 0 < t → HasDerivAt (fun s => H x y s)
              (D.laplacian (fun z => H z y t) x) t) ∧
            (∀ x y t, 0 < t → H x y t = H y x t) ∧
            (∀ x t, 0 < t → ∫ y, H x y t ∂g.volumeMeasure = 1) ∧
            (∀ φ : M → ℝ, Continuous φ → HasCompactSupport φ → ∀ x,
              Tendsto (fun t => ∫ y, H x y t * φ y ∂g.volumeMeasure)
                (𝓝[>] 0) (𝓝 (φ x))) ∧
            (∀ x t, 0 < t → Integrable
              (fun y => (g.edist x y).toReal * H x y t) g.volumeMeasure) ∧
            (∀ x t, 0 < t → t ≤ 1 →
              ∫ y, (g.edist x y).toReal * H x y t ∂g.volumeMeasure ≤ C) ∧
            Tendsto (fun t => ⨆ x,
              ∫ y, (g.edist x y).toReal * H x y t ∂g.volumeMeasure)
              (𝓝[>] 0) (𝓝 0) ∧
            (∀ (u : M → ℝ → ℝ) (y : M),
              ContinuousOn (Function.uncurry u) (univ ×ˢ Ioi 0) →
              (∀ t, 0 < t → ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => u x t)) →
              (∀ x t, 0 < t → HasDerivAt (u x)
                (D.laplacian (fun z => u z t) x) t) →
              (∀ x t, 0 < t → 0 ≤ u x t) →
              (∀ φ : M → ℝ, Continuous φ → HasCompactSupport φ →
                Tendsto (fun t => ∫ z, φ z * u z t ∂g.volumeMeasure)
                  (𝓝[>] 0) (𝓝 (φ y))) →
              ∀ x t, 0 < t → H x y t ≤ u x t) := by
  cases n with
  | zero => omega
  | succ m =>
    by_cases hm : m = 0
    · subst m
      refine ⟨Real.sqrt 2, Real.sqrt_pos.mpr (by norm_num), ?_⟩
      intro M _ _ _ _ _ _ _ _ g hc D _
      obtain ⟨H, hpos, hsmooth, hheat, hsymm, hmass, hinit, hint, hbound, hlim, hmin⟩ :=
        g.exists_minimal_smooth_conservativeHeatKernel_dim_one hc D
      exact ⟨H, hpos, hsmooth, hheat, fun x y t _ => hsymm x y t,
        hmass, hinit, hint, hbound, hlim, hmin⟩
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      obtain ⟨C, hC, hmoment⟩ :=
        exists_dirichletExhaustionKernel_first_moment_bound m K hmpos hK.le
      refine ⟨C, hC, ?_⟩
      intro M _ _ _ _ _ _ _ _ g hc D hsec
      have hRic : ∀ x (v : TangentSpace (𝓡 (m + 1)) x),
          -(m : ℝ) * K * g.inner x v v ≤ D.ricci x v v := by
        intro x v
        simpa [Nat.cast_add] using
          D.ricci_quadratic_lower_bound_of_abs_sectionalCurvature_le x K (hsec x) v
      have hk : 0 ≤ (m : ℝ) * K := mul_nonneg (Nat.cast_nonneg _) hK.le
      have hRic' : ∀ x (v : TangentSpace (𝓡 (m + 1)) x),
          -((m : ℝ) * K) * g.inner x v v ≤ D.ricci x v v := by
        simpa only [neg_mul] using hRic
      obtain ⟨Ω, S, hnest, hcover, hDom, hmono⟩ :=
        D.exists_canonical_dirichletHeatKernel_exhaustion
      let F := fun j => Dirichlet.heatKernelContinuousTime D (S j)
      have hΩmono : Monotone Ω := monotone_nat_of_le_succ fun j =>
        subset_closure.trans (hnest j)
      have hbdd (t : ℝ) (ht : 0 < t) (x y : M) :
          BddAbove (range (fun j => F j t x y)) :=
        D.bddAbove_heatKernelContinuousTime_exhaustion (Nat.succ_pos _) hc hk hRic'
          S hΩmono hcover ht x y
      have hmom := hmoment M g hc D hRic Ω S hΩmono hcover
      refine ⟨fun x y t => dirichletExhaustionKernel F t x y,
        fun x y _ ht => DirichletExhaustion.positive hDom hbdd hΩmono hcover ht x y,
        Dirichlet.contMDiffOn_dirichletExhaustionKernel D hc hk hRic' S hΩmono hcover,
        fun x y _ ht => Dirichlet.hasDerivAt_dirichletExhaustionKernel_laplacian
          D hc hk hRic' S hΩmono hcover x y ht,
        fun x y _ ht => DirichletExhaustion.symmetric hDom ht x y,
        fun x _ ht => D.integral_dirichletExhaustionKernel_eq_one
          hmpos hc hK.le hRic S hΩmono hcover ht x,
        fun φ hφ hφc x => tendsto_integral_iSup_dirichletHeatKernel_initial
          hDom hcover hmono hbdd hφ hφc x,
        fun x _ ht => D.integrable_dirichletExhaustionKernel_distance_all_time
          hmpos hc hK.le hRic S hΩmono hcover ht x,
        fun x t ht ht1 => (hmom.1 x t ht ht1).2, hmom.2, ?_⟩
      intro u y hcont hspace hheat hnonneg htrace x t ht
      exact D.dirichletExhaustionKernel_le_of_nonnegative_heat_solution S
        hcont hspace hheat hnonneg htrace ht x

end PoincareConjecture.RiemannianMetric
