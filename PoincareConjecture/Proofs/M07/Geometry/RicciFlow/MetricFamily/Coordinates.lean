import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.MetricLimit
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Basic









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Bundle
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

theorem isSmoothFamilyOn_of_constant_chart
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hchart : ∀ x y : M,
      chartAt (EuclideanSpace ℝ (Fin n)) x = chartAt (EuclideanSpace ℝ (Fin n)) y)
    (g : ℝ → RiemannianMetric n M) {J : Set ℝ}
    (B : ℝ × M → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) ∞
      B (J ×ˢ univ))
    (hcoeff : ∀ t ∈ J, ∀ (x : M) v w, (g t).inner x v w = B (t, x) v w) :
    IsSmoothFamilyOn g J := by
  have hs : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ,
        EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk'
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ)
        p.2 (B p)) (J ×ˢ univ) := by
    intro p hp
    rw [contMDiffWithinAt_hom_bundle]
    refine ⟨contMDiffWithinAt_snd, ?_⟩
    simpa only [constant_chart_bilinear_coordinates hchart] using hg p hp
  apply hs.congr
  intro p hp
  congr 1
  exact ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w =>
    hcoeff p.1 hp.1 p.2 v w

end PoincareConjecture.RiemannianMetric
