import PoincareConjecture.Proofs.M30.Thm11_1.StaticNullField
import PoincareConjecture.Proofs.M30.Thm11_1.ParallelFlowIsometry
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Completeness
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Flow.BoundedSpeed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set PoincareConjecture.RicciFlow.Splitting
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M30

theorem exists_unitRicciKernel_isometric_globalFlow_of_local_parallel_sections
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (hc : IsCoveringMap (unitRicciKernelProjection D))
    (hcard : ∀ x : M,
      Nat.card (unitRicciKernelProjection D ⁻¹' {x}) = 2)
    (hcomplete : MetricComplete g)
    (hdim : ∀ x : M, ricciNullity D x = 1)
    (hlocal : ∀ p : UnitRicciKernel D,
      ∃ (U : Set M) (V : (y : M) → TangentSpace (𝓡 n) y),
        IsOpen U ∧ p.1.proj ∈ U ∧
        ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V) U ∧
        V p.1.proj = p.1.snd ∧
        ∀ y ∈ U, g.inner y (V y) (V y) = 1 ∧
          (∀ w, D.ricci y (V y) w = 0) ∧
          ∀ w, D.connection V y w = 0) :
    letI := unitRicciKernelChartedSpace D hc
    letI := unitRicciKernelIsManifold D hc
    let g' := unitRicciKernelMetric D hc
    let X := unitRicciKernelField D hc
    ∃ Phi : ℝ → UnitRicciKernel D → UnitRicciKernel D,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞
        (Function.uncurry Phi) ∧
      (∀ p, IsMIntegralCurve (I := 𝓡 n) (fun t => Phi t p) X) ∧
      (∀ p, Phi 0 p = p) ∧
      (∀ s t p, Phi (s + t) p = Phi s (Phi t p)) ∧
      ∀ (t : ℝ) (p : UnitRicciKernel D)
        (v w : TangentSpace (𝓡 n) p),
        g'.inner (Phi t p) (mfderiv (𝓡 n) (𝓡 n) (Phi t) p v)
          (mfderiv (𝓡 n) (𝓡 n) (Phi t) p w) = g'.inner p v w := by
  let := unitRicciKernelChartedSpace D hc
  let := unitRicciKernelIsManifold D hc
  let := unitRicciKernelT3Space D hc
  let g' := unitRicciKernelMetric D hc
  let X := unitRicciKernelField D hc
  have hc' : MetricComplete g' := unitRicciKernelMetric_complete D hc hcard hcomplete
  obtain ⟨hX, hunit, hparallel⟩ :=
    unitRicciKernelField_geometry_of_local_parallel_sections D hc hdim hlocal
  have hspeed (p : UnitRicciKernel D) : g'.tangentNorm p (X p) ≤ 1 := by
    have hp : g'.inner p (X p) (X p) = 1 := hunit p
    simpa only [RiemannianMetric.tangentNorm, hp, Real.sqrt_one] using
      (le_refl (1 : ℝ))
  obtain ⟨Phi, h0, hcurve, hact, hs⟩ :=
    g'.exists_smooth_globalFlow_of_bounded_speed hc' hX (C := 1) zero_le_one hspeed
  refine ⟨Phi, hs, hcurve, h0, hact, ?_⟩
  intro t p v w
  exact flow_preserves_metric_of_parallel g'.leviCivitaData hX hparallel hs hcurve h0 t p v w

end PoincareConjecture.M30
