import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.UniversalProperty
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularLevel







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open Poincare.Geometry.Manifold.RegularLevel
open scoped Manifold ContDiff Topology
namespace Poincare.Geometry.Manifold.RegularLevel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
  (n : ℕ) [Fact (Module.finrank ℝ E = n + 1)]
  (U : Opens M) (hreg : ∀ x ∈ U, mfderiv I 𝓘(ℝ, ℝ) f x ≠ 0) (c : ℝ)


theorem contMDiffOn_into_openLevelSet_iff (F : N → openLevelSet f U c)
    {V : Set N} (hV : IsOpen V) :
    letI := openLevelSetChartedSpace hf U hreg n c
    ContMDiffOn J (𝓡 n) ∞ F V ↔
      ContMDiffOn J I ∞ (openLevelIncl f U c ∘ F) V := by
  let := openLevelSetChartedSpace hf U hreg n c
  constructor
  · intro hF x hx
    exact ((contMDiffAt_into_openLevelSet_iff hf n c U hreg F x).mp
      ((hF x hx).contMDiffAt (hV.mem_nhds hx))).contMDiffWithinAt
  · intro hF x hx
    exact ((contMDiffAt_into_openLevelSet_iff hf n c U hreg F x).mpr
      ((hF x hx).contMDiffAt (hV.mem_nhds hx))).contMDiffWithinAt
end Poincare.Geometry.Manifold.RegularLevel

namespace PoincareConjecture.RiemannianMetric
variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M]
  {f : M → ℝ} (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
  (U : Opens M)
  (hreg : ∀ x ∈ U, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0) (c : ℝ)
local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩


theorem regularLevelMetric_tangentNorm (g : RiemannianMetric (n + 1) M)
    (x : openLevelSet f U c) (v : EuclideanSpace ℝ (Fin n)) :
    letI := openLevelSetChartedSpace hf U hreg n c
    letI := isManifold_openLevelSet hf U hreg n c
    (regularLevelMetric hf U hreg c g).tangentNorm x v =
      g.tangentNorm (openLevelIncl f U c x)
        (mfderiv (𝓡 n) (𝓡 (n + 1)) (openLevelIncl f U c) x v) := rfl


theorem regularLevelMetric_tangentNorm_mfderiv
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    (g : RiemannianMetric (n + 1) M) (F : N → openLevelSet f U c)
    {x : N} (hF : ContMDiffAt J (𝓡 (n + 1)) ∞ (openLevelIncl f U c ∘ F) x)
    (v : TangentSpace J x) :
    letI := openLevelSetChartedSpace hf U hreg n c
    letI := isManifold_openLevelSet hf U hreg n c
    (regularLevelMetric hf U hreg c g).tangentNorm (F x)
        (mfderiv J (𝓡 n) F x v) =
      g.tangentNorm (openLevelIncl f U c (F x))
        (mfderiv J (𝓡 (n + 1)) (openLevelIncl f U c ∘ F) x v) := by
  let := openLevelSetChartedSpace hf U hreg n c
  let := isManifold_openLevelSet hf U hreg n c
  have hFlift := (contMDiffAt_into_openLevelSet_iff hf n c U hreg F x).mpr hF
  rw [regularLevelMetric_tangentNorm, mfderiv_comp x
    ((contMDiff_openLevelIncl hf U hreg n c (F x)).mdifferentiableAt (by simp))
    (hFlift.mdifferentiableAt (by simp))]
  rfl

end PoincareConjecture.RiemannianMetric
