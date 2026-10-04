import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.SourceNames
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Assembly.PositiveComponents.PositiveHistoryPaths
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Seed.Noncollapse.TestHistory

/-!
# Positivity along an included part of the actual backward path

Reverse only the specified age interval and retain the actual history.
Source: MT p. 393; derivations/seed-m15-ancestry.md, Stage I4.
-/

set_option autoImplicit false

open Set

universe u

namespace PoincareMT.M47

open Proofs.M46

/-- Whole-component positivity propagates forward along the actual
path between any two included ages. -/
theorem seedM15_historyPositive_subpath
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (R : M46RegularSpacetimeData W) {T S : ℝ}
    {x y : R.geometry.toLGeometry.Point}
    (path : M14BackwardPath R.geometry.toLGeometry T 0 S x y)
    {s t : ℝ} (hs : s ∈ Icc 0 S) (ht : t ∈ Icc 0 S) (hst : s ≤ t)
    (hpos : HistoryPositive R.history.history (path.curve t)) :
    HistoryPositive R.history.history (path.curve s) := by
  let gamma : ℝ → R.history.generalized.point := fun r => path.curve (t - r)
  have hmaps : MapsTo (fun r : ℝ => t - r) (Icc 0 (t - s)) (Icc 0 S) := by
    intro r hr
    exact ⟨by linarith [hr.2, hs.1], by linarith [hr.1, ht.2]⟩
  have hcont : ContinuousOn gamma (Icc 0 (t - s)) := path.curve_continuous.comp
    (continuous_const.sub continuous_id).continuousOn hmaps
  have hclock : MonotoneOn (fun r => (gamma r).1) (Icc 0 (t - s)) := by
    intro a ha b hb hab
    have hca := path.curve_time (t - a) (hmaps ha)
    have hcb := path.curve_time (t - b) (hmaps hb)
    change (gamma a).1 = T - (t - a) at hca
    change (gamma b).1 = T - (t - b) at hcb
    change (gamma a).1 ≤ (gamma b).1
    rw [hca, hcb]
    linarith
  have hstart : HistoryPositive R.history.history (gamma 0) := by
    simpa only [gamma, sub_zero] using hpos
  have hend := historyPositive_along_path R.history.history (sub_nonneg.mpr hst)
    gamma hcont hclock hstart
  simpa only [gamma, sub_sub_cancel] using hend

end PoincareMT.M47
