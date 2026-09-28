import PoincareConjecture.Proofs.M34.Mathlib.ConstantChartCoordinates
import PoincareConjecture.Proofs.M34.Mathlib.OpenDomainCoordinates
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Pullback
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CanonicalDomain

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M34

variable {n : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) [Nonempty U]
    (e : EuclideanSpace ℝ (Fin n) → N) (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (hle : letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
      IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (fun x : U => e x))

include he

theorem canonicalDomain_pullback_inner (g : RiemannianMetric n N) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ x : U, (g.pullbackOfLocalDiffeomorph (fun y : U => e y) hle).inner x =
      g.pullbackCoefficients e (x : EuclideanSpace ℝ (Fin n)) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro x
  have hed : MDifferentiableAt (𝓡 n) (𝓡 n) e (x : EuclideanSpace ℝ (Fin n)) :=
    ((he x x.property).contMDiffAt (hU.mem_nhds x.property)).mdifferentiableAt (by simp)
  have hd := canonicalOpen_mfderiv_restrict hU (𝓡 n) hed
  ext v w
  change g.inner (e x) (mfderiv (𝓡 n) (𝓡 n) (fun y : U => e y) x v)
    (mfderiv (𝓡 n) (𝓡 n) (fun y : U => e y) x w) =
      g.inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w)
  rw [hd]
  rfl

theorem canonicalDomain_pullback_chart_coefficients (g : RiemannianMetric n N) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ p x : U, (g.pullbackOfLocalDiffeomorph (fun y : U => e y) hle).pullbackCoefficients
      (extChartAt (𝓡 n) p).symm (x : EuclideanSpace ℝ (Fin n)) =
        g.pullbackCoefficients e (x : EuclideanSpace ℝ (Fin n)) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro p x
  rw [RiemannianMetric.pullbackCoefficients_canonicalChart U hU]
  exact canonicalDomain_pullback_inner U hU e he hle g x

theorem canonicalDomain_flow_inner {J : Set ℝ} (F : RicciFlow n N J) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    ∀ (t : ℝ) (x : U),
      ((F.pullbackToCanonicalDomain U hU (fun y : U => e y) hle).metric t).inner x =
        (F.metric t).pullbackCoefficients e (x : EuclideanSpace ℝ (Fin n)) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro t x
  exact canonicalDomain_pullback_inner U hU e he hle (F.metric t) x

theorem canonicalDomain_flow_metric_coordinates {J : Set ℝ} (F : RicciFlow n N J) :
    letI := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    let E := EuclideanSpace ℝ (Fin n)
    let FH := E →L[ℝ] E →L[ℝ] ℝ
    ∀ (t : ℝ) (p x : U),
      ((trivializationAt FH (fun y : U => TangentSpace (𝓡 n) y →L[ℝ]
        TangentSpace (𝓡 n) y →L[ℝ] ℝ) p)
          (TotalSpace.mk' FH x
            (((F.pullbackToCanonicalDomain U hU (fun y : U => e y) hle).metric t).inner x))).2 =
              (F.metric t).pullbackCoefficients e (x : E) := by
  let := hU.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := hU.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  intro E FH t p x
  rw [constantChart_bilinear_coordinates (𝓡 n) (canonicalOpen_chart_eq hU)]
  exact canonicalDomain_flow_inner U hU e he hle F t x

end PoincareConjecture.M34
