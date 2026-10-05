import PoincareLib.Geometry.RicciFlow.Blowup.Construction.ShortTime.StaticLimit.StaticNullField
import PoincareLib.Geometry.RicciFlow.Blowup.Construction.ShortTime.ParallelSections.ParallelFlowIsometry
import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.Completeness
import PoincareLib.Geometry.Riemannian.Flow.BoundedSpeed

/-!
# The all-time isometric flow on the actual Ricci-null cover

Completeness of the supplied base metric gives completeness of its actual
two-sheeted unit Ricci-kernel cover. The retained tautological field is
smooth, unit and parallel by the prescribed local sections, so the bounded
speed theorem constructs one jointly smooth all-time flow. Parallelism
makes every time map preserve the same pullback metric.

This supplies the static flow step for Morgan--Tian Claim 11.7,
pp. 270-271, using the orientation cover of Claim 9.45, pp. 208-209.
The independently reviewed null-cover-global-flow derivation records the
exact retained objects; no global coordinate or product decomposition is
part of this conclusion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set PoincareMT.RicciFlow.Splitting
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M30

/-- Prescribed local parallel null sections produce an all-time isometric
flow of the actual tautological field on the complete unit Ricci-kernel
cover (Claims 9.45 and 11.7, pp. 208-209 and 270-271). -/
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

end PoincareMT.M30
