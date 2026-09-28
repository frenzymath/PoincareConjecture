import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Metric.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Coefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.SingularRegularLimit

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem isSmoothFamilyOn_of_chartCoefficients
    (g : ℝ → RiemannianMetric n M) (J : Set ℝ)
    (hsmooth : ∀ t ∈ J, ∀ q : M,
      ContDiffWithinAt ℝ ∞
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
          (g p.1).pullbackCoefficients (extChartAt (𝓡 n) q).symm p.2)
        (J ×ˢ univ) (t, extChartAt (𝓡 n) q q)) :
    RiemannianMetric.IsSmoothFamilyOn g J := by
  intro p hp
  rw [contMDiffWithinAt_hom_bundle]
  refine ⟨contMDiffWithinAt_snd, ?_⟩
  have hchart : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n))
      𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) ∞
      (fun y : ℝ × M => (y.1, extChartAt (𝓡 n) p.2 y.2)) p :=
    contMDiffAt_fst.prodMk_space
      ((contMDiffAt_extChartAt (I := 𝓡 n) (n := ∞) (x := p.2)).comp p contMDiffAt_snd)
  have hc := (hsmooth p.1 hp.1 p.2).contMDiffWithinAt.comp p
    (hchart.contMDiffWithinAt (s := J ×ˢ univ))
    (show MapsTo (fun y : ℝ × M => (y.1, extChartAt (𝓡 n) p.2 y.2))
      (J ×ˢ univ) (J ×ˢ univ) from fun _ hy => ⟨hy.1, mem_univ _⟩)
  apply hc.congr_of_eventuallyEq
  · filter_upwards [mem_nhdsWithin_of_mem_nhds
      (continuous_snd.isOpen_preimage _ (isOpen_extChartAt_source (I := 𝓡 n) p.2) |>.mem_nhds
        (mem_extChartAt_source (I := 𝓡 n) p.2))] with y hy
    exact tangentBilinear_inCoordinates (fun x => (g y.1).inner x) p.2 y.2 hy
  · exact tangentBilinear_inCoordinates (fun x => (g p.1).inner x) p.2 p.2
      (mem_extChartAt_source p.2)

end PoincareConjecture.SingularRegularLimit
