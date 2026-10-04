import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.Realization
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Compat.GeneralizedEquation
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Spacetime.GeneralizedCylinders

/-!
# Actual spatial inverse coordinates in a generalized flow box

Proposition 16.13, pp. 377-378. The selected coordinate box has the
actual M11 local diffeomorphism. Its smooth inverse and the original
spatial chart recover the physical box coordinate. Time endpoints
retain their selected relative charts throughout this construction.
-/

set_option autoImplicit false
-- All box and inverse maps retain their selected tangent models.
set_option backward.isDefEq.respectTransparency false

open Set Filter Function
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.Proofs.M11
end PoincareMT.Proofs.M11
open Poincare.Spacetime.Realization
namespace PoincareMT.Proofs.M12
end PoincareMT.Proofs.M12
open PoincareMT.EpochExtension.Spacetime
local notation "GeneralizedFlowCarrierConclusion" => PoincareMT.GeneralizedFlowCarrierConclusionWithInterval

namespace PoincareMT.Proofs.M46

open PoincareMT.Proofs.M11 PoincareMT.Proofs.M12

variable {F : GeneralizedRicciFlowData.{u}}
  (R : GeneralizedFlowCarrierConclusion (flowBoxAtlas F))

/-- The actual original box has smooth ambient spatial inverse
coordinates near every included point. Source: Definition 3.38 and
Proposition 16.13, pp. 61 and 377-378. -/
theorem originalBox_spatial_local_inverse (b : F.box_index)
    (p : (R.timeIntervals.interval (boxInterval F b)).Point × (F.box b).carrier.carrier) :
    ∃ phi : R.spacetime.Point → (F.box b).carrier.carrier,
      ContMDiffAt (spacetimeModel 3) (𝓡 3) ∞ phi (originalBoxMap F R b p) ∧
        (fun z => phi (originalBoxMap F R b z)) =ᶠ[𝓝 p] Prod.snd := by
  let c := spatialChartHomeomorph (n := 3) p.2
  have hp : p.2 ∈ c.target := by
    rw [spatialChartHomeomorph_target]
    exact mem_chart_source _ p.2
  let q : (R.timeIntervals.interval (boxInterval F b)).Point × spatialChartDomain p.2 :=
    (p.1, c.symm p.2)
  have hq : (R.boxCylinder ⟨b, p.2⟩).toSpacetime q = originalBoxMap F R b p := by
    rw [← originalBoxMap_chart F R b p.2 q]
    change originalBoxMap F R b (p.1, c (c.symm p.2)) = originalBoxMap F R b p
    rw [c.right_inv hp]
  let hlocal := R.box_localDiffeomorph ⟨b, p.2⟩ q
  let phi : R.spacetime.Point → (F.box b).carrier.carrier :=
    fun z => spatialChartInverse p.2 (hlocal.localInverse z).2
  have hphi : ContMDiffAt (spacetimeModel 3) (𝓡 3) ∞ phi
      (originalBoxMap F R b p) := by
    rw [← hq]
    exact (spatialChartInverse_smooth p.2 _).comp _
      (contMDiffAt_snd.comp _ hlocal.localInverse_contMDiffAt)
  have hc : ContinuousAt (fun z :
      (R.timeIntervals.interval (boxInterval F b)).Point × (F.box b).carrier.carrier =>
        (z.1, c.symm z.2)) p :=
    continuous_fst.continuousAt.prodMk
      (((spatialChartHomeomorph_inverse_smooth p.2).contMDiffAt
        (c.open_target.mem_nhds hp)).continuousAt.comp continuous_snd.continuousAt)
  have hleft := hc.tendsto.eventually hlocal.localInverse_eventuallyEq_left
  refine ⟨phi, hphi, ?_⟩
  filter_upwards [hleft, (c.open_target.preimage continuous_snd).mem_nhds hp]
    with z hz hzsrc
  dsimp only [Function.comp_apply, id_eq] at hz
  have hchart : originalBoxMap F R b z =
      (R.boxCylinder ⟨b, p.2⟩).toSpacetime (z.1, c.symm z.2) := by
    rw [← originalBoxMap_chart F R b p.2 (z.1, c.symm z.2)]
    change originalBoxMap F R b z = originalBoxMap F R b (z.1, c (c.symm z.2))
    rw [c.right_inv hzsrc]
  change spatialChartInverse p.2 (hlocal.localInverse (originalBoxMap F R b z)).2 = z.2
  rw [hchart, hz]
  exact c.right_inv hzsrc

end PoincareMT.Proofs.M46
