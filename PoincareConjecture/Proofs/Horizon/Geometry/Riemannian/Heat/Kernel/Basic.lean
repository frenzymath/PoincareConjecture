import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Data
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Existence
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ZeroDimensional


set_option autoImplicit false

open MeasureTheory Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]


theorem exists_conservativeHeatKernelData
    (g : RiemannianMetric n M) [PreconnectedSpace M] [NoncompactSpace M]
    (hcomplete : MetricComplete g) {K : ℝ} (hK : 0 < K)
    (D : LeviCivitaData g)
    (hcurv : ∀ x u v, |D.sectionalCurvature x u v| ≤ K) :
    Nonempty (ConservativeHeatKernelData g) := by
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst n
    let : Subsingleton M := Poincare.subsingleton_of_preconnected_euclidean_zero M
    exact noncompact_univ M isCompact_univ
  obtain ⟨C, hC, hkernel⟩ := exists_minimal_smooth_conservativeHeatKernel n K hn hK
  obtain ⟨H, hpos, hsmooth, hheat, _, hmass, hinit, hint, hbound, hlim, _⟩ :=
    hkernel M g hcomplete D hcurv
  refine ⟨{
    connection := D
    kernel := H
    positive := hpos
    smooth := ?_
    timeDifferentiable := fun x y t ht => (hheat x y t ht).differentiableAt
    mass_one := hmass
    initial := hinit
    heat_equation := fun x y t ht => (hheat x y t ht).deriv
    first_moment_integrable := hint
    first_moment_bound := ⟨C, hC, hbound⟩
    first_moment_tendsto_zero := hlim }⟩
  intro x y t ht
  have hmap : ContMDiff (𝓡 n) ((𝓘(ℝ, ℝ).prod (𝓡 n)).prod (𝓡 n)) ∞
      (fun z : M => ((t, z), y)) :=
    (contMDiff_const.prodMk contMDiff_id).prodMk contMDiff_const
  have h := hsmooth.comp hmap.contMDiffOn (s := Set.univ)
    (fun z _ => ⟨⟨ht, Set.mem_univ z⟩, Set.mem_univ y⟩)
  exact (contMDiffOn_univ.mp h).contMDiffAt

end PoincareConjecture.RiemannianMetric
