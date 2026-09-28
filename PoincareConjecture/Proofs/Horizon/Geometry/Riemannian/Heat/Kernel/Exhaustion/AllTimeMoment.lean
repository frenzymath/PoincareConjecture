import PoincareConjecture.Proofs.Horizon.MeasureTheory.Integral.KernelMoment
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Moment

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.LeviCivitaData

theorem integrable_dirichletExhaustionKernel_distance_all_time
    {m : ℕ} (hm : 0 < m) {M : Type u} [TopologicalSpace M] [T3Space M]
    [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
    [IsManifold (𝓡 (m + 1)) ∞ M] [PreconnectedSpace M]
    {g : RiemannianMetric (m + 1) M} (D : LeviCivitaData g)
    (hc : MetricComplete g) {κ : ℝ} (hκ : 0 ≤ κ)
    (hRic : ∀ x (v : TangentSpace (𝓡 (m + 1)) x),
      -(m : ℝ) * κ * g.inner x v v ≤ D.ricci x v v)
    {Ω : ℕ → Set M} (S : ∀ j, Poincare.Manifold.SmoothDomain (m + 1) (Ω j))
    (hΩmono : Monotone Ω) (hcover : (⋃ j, Ω j) = univ)
    {t : ℝ} (ht : 0 < t) (x : M) :
    Integrable (fun y => (g.edist x y).toReal *
      dirichletExhaustionKernel (fun j => Dirichlet.heatKernelContinuousTime D (S j))
        t x y) g.volumeMeasure := by
  let : SecondCountableTopology M := g.secondCountableTopology
  let K := fun j => Dirichlet.heatKernelContinuousTime D (S j)
  have hK : ∀ j, Dirichlet.IsDirichletHeatKernel D (Ω j) (K j) :=
    fun j => Dirichlet.heatKernelContinuousTime_isDirichletHeatKernel D (S j)
  have hmono := fun (s : ℝ) (hs : 0 < s) z y =>
    D.monotone_heatKernelContinuousTime_exhaustion S hΩmono hs z y
  have hbdd : ∀ s, 0 < s → ∀ z y, BddAbove (range (fun j => K j s z y)) := by
    intro s hs z y
    exact D.bddAbove_heatKernelContinuousTime_exhaustion (by omega) hc
      (k := (m : ℝ) * κ) (by positivity)
      (fun w v => by simpa [mul_assoc] using hRic w v) S hΩmono hcover hs z y
  obtain ⟨C, _, hmoment⟩ := exists_dirichletExhaustionKernel_first_moment_bound m κ hm hκ
  have hsmall := (hmoment M g hc D hRic Ω S hΩmono hcover).1
  have hd : Measurable (fun p : M × M => (g.edist p.1 p.2).toReal) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (m + 1)))
        (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 (m + 1)) M
    change Measurable (fun p : M × M => (edist p.1 p.2).toReal)
    exact (measurable_fst.edist measurable_snd).ennreal_toReal
  exact Poincare.MeasureTheory.integrable_cost_semigroup_of_small_time
    hd (fun _ _ => ENNReal.toReal_nonneg) g.toReal_edist_triangle
    (fun s hs => by
      convert measurable_dirichletExhaustionKernel hK hbdd hs using 1 <;> rfl)
    (fun s hs => DirichletExhaustion.nonneg hK hbdd hs)
    (fun s hs => DirichletExhaustion.mass hK hmono hbdd hs)
    (fun s r hs hr => DirichletExhaustion.semigroup hK hmono hbdd hs hr)
    (fun s hs hs1 z => hsmall z s hs hs1) ht x

end PoincareConjecture.LeviCivitaData
