import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.CompactImage
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.RegularLevelMap
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Coarea.LevelVolume

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal NNReal

namespace PoincareConjecture.RiemannianMetric
open Poincare.Geometry.Manifold.RegularLevel

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n+1))) M] [IsManifold (𝓡 (n+1)) ∞ M]
  (g : RiemannianMetric (n+1) M)
  {f : M → ℝ} (hf : ContMDiff (𝓡 (n+1)) 𝓘(ℝ,ℝ) ∞ f)
  (U : TopologicalSpace.Opens M)
  (hreg : ∀ x ∈ U, mfderiv (𝓡 (n+1)) 𝓘(ℝ,ℝ) f x ≠ 0)
  (W : TopologicalSpace.Opens M)
  (hregW : ∀ x ∈ W, mfderiv (𝓡 (n+1)) 𝓘(ℝ,ℝ) f x ≠ 0)
  (a b : ℝ)

local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n+1))) = n+1) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem regularLevelVolume_image_le_of_ambient_tangentNorm_le_on_compact
    (F : openLevelSet f U a → openLevelSet f W b)
    {V s : Set (openLevelSet f U a)} (hV : IsOpen V)
    (hs : IsCompact s) (hsV : s ⊆ V) {C : ℝ} (hC : 0 < C) :
    letI := openLevelSetChartedSpace hf U hreg n a
    letI := isManifold_openLevelSet hf U hreg n a
    letI := openLevelSetChartedSpace hf W hregW n b
    letI := isManifold_openLevelSet hf W hregW n b
    ContMDiffOn (𝓡 n) (𝓡 (n+1)) ∞ (openLevelIncl f W b ∘ F) V →
    (∀ x ∈ V, ∀ v : TangentSpace (𝓡 n) x,
      g.tangentNorm (openLevelIncl f W b (F x))
        (mfderiv (𝓡 n) (𝓡 (n+1)) (openLevelIncl f W b ∘ F) x v) ≤
          C * g.tangentNorm (openLevelIncl f U a x)
            (mfderiv (𝓡 n) (𝓡 (n+1)) (openLevelIncl f U a) x v)) →
    g.regularLevelVolume hf W hregW b (F '' s) ≤
      ENNReal.ofReal C ^ n * g.regularLevelVolume hf U hreg a s := by
  let := openLevelSetChartedSpace hf U hreg n a
  let := isManifold_openLevelSet hf U hreg n a
  let := openLevelSetChartedSpace hf W hregW n b
  let := isManifold_openLevelSet hf W hregW n b
  intro hF hbound
  have hFlift := (contMDiffOn_into_openLevelSet_iff hf n W hregW b F hV).mpr hF
  apply (regularLevelMetric hf U hreg a g).volumeMeasure_image_le_of_tangentNorm_le_on_compact
    (regularLevelMetric hf W hregW b g) hV hs hsV (hFlift.of_le (by simp)) hC
  intro x hx v
  rw [regularLevelMetric_tangentNorm_mfderiv hf W hregW b g F
    (hF.contMDiffAt (hV.mem_nhds hx)) v, regularLevelMetric_tangentNorm]
  exact hbound x hx v

end PoincareConjecture.RiemannianMetric
