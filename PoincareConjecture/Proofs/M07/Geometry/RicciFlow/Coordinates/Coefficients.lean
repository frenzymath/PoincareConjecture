import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Convergence.CoordinateRegularity
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem contDiffOn_pullbackCoefficients (F : RicciFlow n M J) (hJ : IsOpen J)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U) :
    ContDiffOn ℝ ∞ (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
      (F.metric z.1).pullbackCoefficients e z.2) (J ×ˢ U) := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w p hp
  apply ContDiffAt.contDiffWithinAt
  let f : ℝ × EuclideanSpace ℝ (Fin n) → M := fun z => e z.2
  have hf {z : ℝ × EuclideanSpace ℝ (Fin n)} (hz : z.2 ∈ U) :
      ContMDiffAt 𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin n)) (𝓡 n) ∞ f z :=
    (he.contMDiffAt (hU.mem_nhds hz)).comp z contDiffAt_snd.contMDiffAt
  apply (F.contDiffAt_family_pullback_inner (hJ.mem_nhds hp.1)
    (hf hp.2) (0, v) (0, w)).congr_of_eventuallyEq
  filter_upwards [continuousAt_snd.preimage_mem_nhds (hU.mem_nhds hp.2)] with z hz
  have hv := RiemannianMetric.mfderiv_slice_apply ((hf hz).mdifferentiableAt (by simp)) v
  have hw := RiemannianMetric.mfderiv_slice_apply ((hf hz).mdifferentiableAt (by simp)) w
  rw [← hv, ← hw]
  rfl

end PoincareConjecture.RicciFlow
