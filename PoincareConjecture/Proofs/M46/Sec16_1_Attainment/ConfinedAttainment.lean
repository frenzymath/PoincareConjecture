import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.WeakLimitAttainment
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_4_MinimizingSequence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}

theorem actionConfinement_attained (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {T start tau : ℝ} {x y : G.Point} (C : ActionConfinement G T start x)
    (htau : 0 < tau) (htauStart : tau ≤ T - start)
    (p0 : M14BackwardPath G T 0 tau x y) (hp0 : M14BackwardLAction G p0 < C.barrier) :
    M14AttainedDomain G T 0 tau x y := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (spacetimeModel 3) : G.Point → Type _) :=
    ⟨(M14.auxiliarySpacetimeMetric G.spacetime).toRiemannianMetric⟩
  let : EMetricSpace G.Point := .ofRiemannianMetric (spacetimeModel 3) G.Point
  obtain ⟨hfinite, p, D, hD, hp, _, haction, henergy⟩ :=
    exists_confined_minimizing_sequence hM12 C htau htauStart p0 hp0
  obtain ⟨alpha, phi, hphi, hlim, _, hclock, hx, hy⟩ :=
    backward_squarePaths_uniform_subsequence p hD henergy C.cage_compact (fun k => (hp k).2)
  let gamma (s : ℝ) := alpha (projIcc 0 (Real.sqrt tau) (Real.sqrt_nonneg tau) s)
  have hgammaEq (s : ℝ) (hs : s ∈ Icc 0 (Real.sqrt tau)) : gamma s = alpha ⟨s, hs⟩ := by
    simp only [gamma, projIcc_of_mem _ hs]
  have hgammaClock (s : ℝ) (hs : s ∈ Icc 0 (Real.sqrt tau)) :
      G.spacetime.timeFunction (gamma s) = T - s ^ 2 := by
    rw [hgammaEq s hs]
    exact hclock ⟨s, hs⟩
  have hgammax : gamma 0 = x :=
    (hgammaEq 0 ⟨le_rfl, Real.sqrt_nonneg tau⟩).trans hx
  have hgammay : gamma (Real.sqrt tau) = y :=
    (hgammaEq _ ⟨Real.sqrt_nonneg tau, le_rfl⟩).trans hy
  obtain ⟨hgamma, hlimGamma⟩ := clamp_uniform_limit (Real.sqrt_nonneg tau) alpha
    (fun k s => (p (phi k)).curve (s ^ 2)) hlim
  have htransport : ∀ x' y' : G.Point, gamma 0 = x' → gamma (Real.sqrt tau) = y' →
      M14FiniteValueDomain G T 0 tau x' y' →
      (∀ q : ℕ → M14BackwardPath G T 0 tau x' y',
        TendstoUniformlyOn (fun k s => (q k).curve (s ^ 2)) gamma atTop (Icc 0 (Real.sqrt tau)) →
        (∀ k, IntervalIntegrable (M14.pathSquareKinetic (q k)) volume 0 (Real.sqrt tau) ∧
          (∫ s in 0..Real.sqrt tau, M14.pathSquareKinetic (q k) s) ≤ D) →
        Tendsto (fun k => M14BackwardLAction G (q k)) atTop (𝓝 (M14ActionValue G T 0 tau x' y')) →
        M14AttainedDomain G T 0 tau x' y') := by
    intro x' y' hx' hy' hf q hq hqenergy hqaction
    subst x'
    subst y'
    exact weak_limit_attained hM12 htau gamma hgamma hgammaClock q hf hq hqenergy hqaction
  exact htransport x y hgammax hgammay hfinite (fun k => p (phi k)) hlimGamma
    (fun k => henergy (phi k)) (haction.comp hphi.tendsto_atTop)

end PoincareConjecture.Proofs.M46
