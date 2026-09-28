import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_SphereJetMargin
import PoincareConjecture.Proofs.M44.Mathlib.SectionalPlane

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M44

open SpacetimeBounds

local notation "E" => EuclideanSpace ℝ (Fin 3)

noncomputable local instance pullbackPlaneCoefficientNormedGroup :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance pullbackPlaneCoefficientNormedSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

theorem jetCurvature_pullbackCoefficients
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    {f : E → M} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible)
    {x : E} (hx : x ∈ U) (u w v z : E) :
    jetCurvature (metricTwoJet (g.pullbackCoefficients f) x) u w v z =
      D.curvatureTensor (f x) (mfderiv (𝓡 3) (𝓡 3) f x u)
        (mfderiv (𝓡 3) (𝓡 3) f x w) (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x z) := by
  obtain ⟨gE, DE, V, hV, hxV, hVU, hmetric⟩ :=
    RiemannianMetric.exists_local_realization hU hx (g.pullbackCoefficients f)
      (fun y hy => (g.contDiffAt_pullbackCoefficients
        (hf.contMDiffAt (hU.mem_nhds hy))).contDiffWithinAt)
      (fun y _ a b => g.symm (f y) _ _)
      (fun y hy a ha => by
        apply g.pos (f y)
        intro hz
        apply ha
        apply (hinv y hy).injective
        rw [map_zero]
        exact hz)
  have heq : gE.euclideanCoefficients =ᶠ[𝓝 x] g.pullbackCoefficients f :=
    eventually_of_mem (hV.mem_nhds hxV) hmetric
  have htwo : metricTwoJet gE.euclideanCoefficients x =
      metricTwoJet (g.pullbackCoefficients f) x := by
    simp only [metricTwoJet, heq.eq_of_nhds, heq.fderiv_eq,
      (heq.fderiv (𝕜 := ℝ)).fderiv_eq]
  rw [← htwo, jetCurvature_metricTwoJet DE]
  exact DE.curvatureTensor_eq_of_local_isometry D hV (hf.mono hVU)
    (fun y hy a b => congrArg (fun B => B a b) (hmetric y hy)) hxV u w v z

theorem sectional_lower_of_pullback_twoJet
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    {f : E → M} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible)
    {x : E} (hx : x ∈ U) (k : ℝ) (u v : E)
    (hJ : metricTwoJet (g.pullbackCoefficients f) x ∈ sectionalJetLowerRegion k u v) :
    let L := mfderiv (𝓡 3) (𝓡 3) f x
    0 < g.inner (f x) (L u) (L u) * g.inner (f x) (L v) (L v) -
      (g.inner (f x) (L u) (L v)) ^ 2 ∧
      k < D.sectionalCurvature (f x) (L u) (L v) := by
  refine ⟨hJ.2.1, ?_⟩
  unfold LeviCivitaData.sectionalCurvature
  apply (lt_div_iff₀ hJ.2.1).mpr
  rw [← jetCurvature_pullbackCoefficients g D hU hf hinv hx]
  exact hJ.2.2

theorem sectional_lower_on_physical_plane
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g) (x : M)
    {u v p q : TangentSpace (𝓡 3) x} {k : ℝ}
    (huv : 0 < g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2)
    (hlower : k < D.sectionalCurvature x u v)
    (hp : p ∈ Submodule.span ℝ ({u, v} : Set (TangentSpace (𝓡 3) x)))
    (hq : q ∈ Submodule.span ℝ ({u, v} : Set (TangentSpace (𝓡 3) x)))
    (hpq : 0 < g.inner x p p * g.inner x q q - (g.inner x p q) ^ 2) :
    k < D.sectionalCurvature x p q := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply (lt_div_iff₀ hpq).mpr
  exact sectional_lower_of_mem_span_pair (M13.curvatureTensorLinear D x)
    (fun a b c d => D.curvatureTensor_swap_first x a b c d)
    (fun a b c d => D.curvatureTensor_swap_last x a b c d)
    ((lt_div_iff₀ huv).mp hlower) hp hq hpq

end PoincareConjecture.M44
