import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.Coordinates
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.Metric



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Poincare.Gluing Bundle
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.ChartDistance

theorem canonicalMetric_isSmoothFamilyOn_of_coefficients
    {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)] (i : ι)
    (g : ℝ → CanonicalMetric U hU i) {J : Set ℝ}
    (B : ℝ × EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B (J ×ˢ U i))
    (hcoeff :
      letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
      ∀ t ∈ J, ∀ (x : Piece U i) v w, (g t).inner x v w = B (t, x) v w) :
    letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
    RiemannianMetric.IsSmoothFamilyOn g J := by
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  apply RiemannianMetric.isSmoothFamilyOn_of_constant_chart (fun _ _ => rfl) g
    (fun p => B (p.1, p.2)) ?_ hcoeff
  have hv := contMDiff_isOpenEmbedding (I := 𝓡 n) (n := ∞)
    (hU i).isOpenEmbedding_subtypeVal
  have hmap : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) ∞
      (fun p : ℝ × Piece U i => (p.1, (p.2 : EuclideanSpace ℝ (Fin n)))) :=
    contMDiff_fst.prodMk_space (hv.comp contMDiff_snd)
  exact hB.contMDiffOn.comp hmap.contMDiffOn (fun p hp => ⟨hp.1, p.2.property⟩)

end PoincareConjecture.ChartDistance
