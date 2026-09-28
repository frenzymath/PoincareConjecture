import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.PlanarCircleObservation

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem circleProduct_observation_with_current
    (P : M62.CircleProductData F circumference) :
    ∃ (d : ℕ) (e : P.charts.Point → EuclideanSpace ℝ (Fin d))
      (R : EuclideanSpace ℝ (Fin d) →L[ℝ] LoopPlane),
      ContMDiff (𝓡 (n + 1)) (𝓡 d) ∞ e ∧ IsClosedEmbedding e ∧
      M60.SUChartReadable (n := n + 1) e ∧
      (∀ q, R (e q) = planarCircleObservation q.2) ∧ ∀ q, ‖R (e q)‖ = 1 := by
  let := P.circle.chartedSpace
  let := P.charts.chartedSpace
  let := P.charts.isManifold
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  have hsnd : ContMDiff (𝓡 (n + 1)) (𝓡 1) ∞
      (Prod.snd : P.charts.Point → P.circle.Point) :=
    contMDiff_snd.comp P.charts.to_product_smooth
  have hf : ContMDiff (𝓡 (n + 1)) (𝓡 2) ∞
      (fun q : P.charts.Point => planarCircleObservation q.2) :=
    (planarCircleObservation_contMDiff P.circle).comp hsnd
  obtain ⟨d, e, R, he, hei, hread, hR⟩ :=
    chartReadable_observation_with_planar_projection _ hf
  refine ⟨d, e, R, he, hei, hread, ?_, ?_⟩
  · intro q
    exact congrFun hR q
  · intro q
    rw [show R (e q) = planarCircleObservation q.2 from congrFun hR q]
    exact planarCircleObservation_norm P.circle q.2

end PoincareConjecture.M64
