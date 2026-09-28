import PoincareConjecture.Proofs.M03.ConnectionRateRicciSmoothness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Local.Metric.RicciPairRegularity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Local.Energy.Comparison.ScalarMixedDerivative

set_option autoImplicit false
set_option maxHeartbeats 1800000

open scoped Manifold ContDiff Bundle Topology
open Set

universe u

namespace PoincareConjecture.RicciFlow.Local

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem connection_rate_ricci_pair_smooth
    {J : Set ℝ} (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J)
    {U : Set M} (hU : IsOpen U)
    (Y Z : (y : M) → TangentSpace (𝓡 n) y)
    (hY : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) U)
    (hZ : ContMDiffOn (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) U)
    {x : M} (hx : x ∈ U) :
    ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => (F.connection t).ricci y (Y y) (Z y)) x := by
  let c := extChartAt (𝓡 n) x
  have hcx : c.symm (c x) = x := c.left_inv (mem_extChartAt_source x)
  have hcxt : c x ∈ c.target := mem_extChartAt_target x
  have hc : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ c.symm (c x) :=
    (contMDiffOn_extChartAt_symm (I := 𝓡 n) x).contMDiffAt
      (extChartAt_target_mem_nhds' hcxt)
  have hn : interior J ×ˢ (c.target ∩ c.symm ⁻¹' U) ∈ 𝓝 (t, c x) :=
    prod_mem_nhds (isOpen_interior.mem_nhds ht)
      (Filter.inter_mem (extChartAt_target_mem_nhds' hcxt)
        (hc.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simpa only [hcx] using hx))))
  have hh := (contDiffOn_ricciFlow_ricci_chart_pair F hU Y Z hY hZ x).contDiffAt hn
  have hs := hh.comp (c x) (contDiffAt_const.prodMk contDiffAt_id)
  rw [contMDiffAt_iff_source]
  rw [(𝓡 n).range_eq_univ, contMDiffWithinAt_univ]
  change ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
    ((fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      (F.connection p.1).ricci (c.symm p.2)
        (Y (c.symm p.2)) (Z (c.symm p.2))) ∘ fun z => (t, z)) (c x)
  exact hs.contMDiffAt

end PoincareConjecture.RicciFlow.Local
