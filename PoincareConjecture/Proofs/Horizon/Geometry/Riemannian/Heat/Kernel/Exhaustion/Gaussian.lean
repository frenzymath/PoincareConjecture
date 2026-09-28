import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Gaussian.Estimate
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Gaussian.TwoBall
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.IntegralLimit
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Spectral
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.GlobalHarnack












set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped Manifold ContDiff Topology Bundle ENNReal

universe u

namespace PoincareConjecture.LeviCivitaData

theorem measurable_dirichletExhaustionKernel
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] {g : RiemannianMetric n M}
    {D : LeviCivitaData g} {Ω : ℕ → Set M}
    {K : ℕ → ℝ → M → M → ℝ}
    (hK : ∀ j, Dirichlet.IsDirichletHeatKernel D (Ω j) (K j))
    (hbdd : ∀ t, 0 < t → ∀ x y, BddAbove (range (fun j => K j t x y)))
    {t : ℝ} (ht : 0 < t) :
    Measurable (fun p : M × M => dirichletExhaustionKernel K t p.1 p.2) := by
  have hlsc : LowerSemicontinuous
      (fun p : (M × M) × Ioi (0 : ℝ) =>
        dirichletExhaustionKernel K p.2 p.1.1 p.1.2) :=
    DirichletExhaustion.lowerSemicontinuous hK hbdd
  have hm : Measurable
      (fun q : (M × M) × Ioi (0 : ℝ) =>
        dirichletExhaustionKernel K q.2 q.1.1 q.1.2) := hlsc.measurable
  have hcst : Measurable (fun p : M × M =>
      (p, (⟨t, ht⟩ : Ioi (0 : ℝ)))) :=
    Measurable.prodMk measurable_id measurable_const
  change Measurable ((fun q : (M × M) × Ioi (0 : ℝ) =>
    dirichletExhaustionKernel K q.2 q.1.1 q.1.2) ∘ (fun p : M × M =>
    (p, (⟨t, ht⟩ : Ioi (0 : ℝ)))))
  exact hm.comp hcst

theorem exists_dirichletExhaustionKernel_gaussian_bound
    (m : ℕ) (κ : ℝ) (hm : 0 < m) (hκ : 0 ≤ κ) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M]
        [MeasurableSpace M] [BorelSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
        [IsManifold (𝓡 (m + 1)) ∞ M] [PreconnectedSpace M]
        (g : RiemannianMetric (m + 1) M), MetricComplete g →
        ∀ D : LeviCivitaData g,
          (∀ x (v : TangentSpace (𝓡 (m + 1)) x),
            -(m : ℝ) * κ * g.inner x v v ≤ D.ricci x v v) →
          ∀ (Ω : ℕ → Set M)
            (S : ∀ j, Poincare.Manifold.SmoothDomain (m + 1) (Ω j)),
            Monotone Ω → (⋃ j, Ω j) = univ →
            ∀ t, 0 < t → t ≤ 1 → ∀ x y,
              dirichletExhaustionKernel
                  (fun j => Dirichlet.heatKernelContinuousTime D (S j)) t x y ≤
                A / g.volumeMeasure.real (g.ball x (Real.sqrt t)) *
                  Real.exp (-(g.edist x y).toReal ^ 2 / (192 * t)) := by
  obtain ⟨A, hA, hconst⟩ :=
    PoincareConjecture.RiemannianMetric.exists_gaussian_bound_of_double_ball_estimates
      (m + 1) κ
        (2 * ((m + 1 : ℕ) : ℝ) * ((m : ℝ) * κ))
        (by omega) hκ (by positivity)
  refine ⟨A, hA, ?_⟩
  intro M _ _ _ _ _ _ _ g hc D hRic Ω S hΩmono hcover t ht ht1 x y
  let K := fun j => Dirichlet.heatKernelContinuousTime D (S j)
  have hK : ∀ j, Dirichlet.IsDirichletHeatKernel D (Ω j) (K j) :=
    fun j => Dirichlet.heatKernelContinuousTime_isDirichletHeatKernel D (S j)
  have hbdd : ∀ s, 0 < s → ∀ p q,
      BddAbove (range (fun j => K j s p q)) := by
    intro s hs p q
    exact D.bddAbove_heatKernelContinuousTime_exhaustion (by omega) hc
      (k := (m : ℝ) * κ) (by positivity)
      (fun z v => by simpa [mul_assoc] using hRic z v) S hΩmono hcover hs p q
  have hmono : ∀ s, 0 < s → ∀ p q, Monotone (fun j => K j s p q) := by
    intro s hs p q
    exact D.monotone_heatKernelContinuousTime_exhaustion S hΩmono hs p q
  let H := dirichletExhaustionKernel K
  have hmass : ∀ s, 0 < s → ∀ p,
      Integrable (H s p) g.volumeMeasure ∧
        (∫ q, H s p q ∂g.volumeMeasure) ≤ 1 := by
    intro s hs p
    exact DirichletExhaustion.mass hK hmono hbdd hs p
  have hnonneg : ∀ s, 0 < s → ∀ p q, 0 ≤ H s p q := by
    intro s hs p q
    exact DirichletExhaustion.nonneg hK hbdd hs p q
  have hsymm : ∀ s, 0 < s → ∀ p q, H s p q = H s q p := by
    intro s hs p q
    exact DirichletExhaustion.symmetric hK hs p q
  have hmeas : ∀ s, 0 < s → Measurable (fun p : M × M => H s p.1 p.2) := by
    intro s hs
    let : SecondCountableTopology M := g.secondCountableTopology
    exact measurable_dirichletExhaustionKernel hK hbdd hs
  have hharnack : ∀ a b, 0 < a → a < b → ∀ p q z,
      H a p z ≤ H b q z * Real.exp
        (2 * ((m + 1 : ℕ) : ℝ) * Real.log (b / a) +
          2 * ((m + 1 : ℕ) : ℝ) * ((m : ℝ) * κ) * (b - a) +
          (g.edist p q).toReal ^ 2 / (2 * (b - a))) := by
    intro a b ha hab p q z
    exact dirichletExhaustionKernel_global_harnack_of_ricci_lower D hm hc hκ hRic
      (fun j => (S j).isOpen) hΩmono hcover hK hmono ha hab p q z
  have hdouble : ∀ s, 0 < s → ∀ p q,
      (∫ z in g.ball p (Real.sqrt s), ∫ w in g.ball q (Real.sqrt s),
        H (3 * s) z w ∂g.volumeMeasure ∂g.volumeMeasure) ≤
      Real.sqrt (g.volumeMeasure.real (g.ball p (Real.sqrt s))) *
        Real.sqrt (g.volumeMeasure.real (g.ball q (Real.sqrt s))) *
          Real.exp (-(max ((g.edist p q).toReal - 2 * Real.sqrt s) 0) ^ 2 /
            (48 * s)) := by
    intro s hs p q
    apply DirichletExhaustion.setIntegral_setIntegral_le_of_uniform_bound
      hK hmono hbdd
      (g.volumeMeasure_ball_lt_top hc p (Real.sqrt s))
      (g.volumeMeasure_ball_lt_top hc q (Real.sqrt s)) (by positivity)
    intro j
    simpa only [K, H, show 16 * (3 * s) = 48 * s by ring] using
      (Dirichlet.setIntegral_setIntegral_heatKernelContinuousTime_ball_le
        D (S j) hc (t := 3 * s) (by positivity) p q (Real.sqrt s))
  have hRic' : ∀ z (v : TangentSpace (𝓡 (m + 1)) z),
      -((((m + 1 : ℕ) : ℝ) - 1) * κ) * g.inner z v v ≤ D.ricci z v v := by
    intro z v
    simpa [Nat.cast_add] using hRic z v
  exact hconst M g hc D hRic' H hmeas hnonneg hsymm
    (fun s hs p => (hmass s hs p).1) (fun s hs p => (hmass s hs p).2)
    hharnack hdouble t ht ht1 x y

end PoincareConjecture.LeviCivitaData
