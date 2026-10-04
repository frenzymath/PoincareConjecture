import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Endpoint.LineEndpointFamily
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.SquareRoot.Families.SquareFamilyRestriction

/-!
# The actual smooth broken cost

Morgan-Tian Proposition 6.30, pp. 118-119. The cost sums the genuine
prefix action and a fixed-parameter continuation action at their
common moving endpoint. Its shifted coordinates center the original
family on the zero vertical parameter.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {f : ℝ × ℝ → G.Point} {U : Set ℝ} {T b c : ℝ}
  {j : G.gaugeCover.index}
  {lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
    G.gaugeCover.spatial j}

namespace GaugeEndpointFamily

variable (D : GaugeEndpointFamily f U T 0 b c 0 j lift)

/-- The actual prefix square action, Proposition 6.30, pp. 118-119. -/
noncomputable def prefixAction (z : ℝ × EuclideanSpace ℝ (Fin n)) : ℝ :=
  squareFamilyAction G D.family (Icc 0 b) 0 c z

/-- The actual continuation square action with its initial-vector
parameter fixed at zero, Proposition 6.30, pp. 118-119. -/
noncomputable def tailAction (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  squareFamilyAction G D.family (Icc 0 b) c b (0, y)

/-- The actual prefix-plus-tail cost with the original coordinate
diagonal shifted to vertical zero, Proposition 6.30, pp. 118-119. -/
noncomputable def cost (z : ℝ × EuclideanSpace ℝ (Fin n)) : ℝ :=
  D.prefixAction (z.1, (lift (f (c, z.1))).2.val + z.2) +
    D.tailAction ((lift (f (c, z.1))).2.val + z.2)

/-- The actual prefix action is smooth at every valid endpoint-family
parameter, Lemma 6.22 and Proposition 6.30, pp. 115-116, 118-119. -/
theorem prefixAction_contDiffAt (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hc : c ∈ Ioo 0 b) {z : ℝ × EuclideanSpace ℝ (Fin n)} (hz : z ∈ D.parameters) :
    ContDiffAt ℝ ∞ D.prefixAction z :=
  (squareFamilyAction_contDiffOn hM12 (hc.1.trans hc.2) D.parameters_open
    D.smooth (Ioo_subset_Icc_self hc) z hz).contDiffAt (D.parameters_open.mem_nhds hz)

/-- The fixed-parameter continuation action is smooth at every valid
meeting coordinate, Proposition 6.30, pp. 118-119. -/
theorem tailAction_contDiffAt (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hc : c ∈ Ioo 0 b) {y : EuclideanSpace ℝ (Fin n)} (hy : (0, y) ∈ D.parameters) :
    ContDiffAt ℝ ∞ D.tailAction y :=
  ((squareFamilyAction_interval_contDiffOn hM12 (hc.1.trans hc.2) D.parameters_open
    D.smooth (Ioo_subset_Icc_self hc) ⟨(hc.1.trans hc.2).le, le_rfl⟩ (0, y) hy).contDiffAt
      (D.parameters_open.mem_nhds hy)).comp y (contDiffAt_const.prodMk contDiffAt_id)

/-- The genuine broken cost is smooth at its central parameter,
including physical endpoints of the full time interval,
Proposition 6.30, pp. 118-119. -/
theorem cost_contDiffAt (hM12 : GeneralizedRicciGaugeTheory.{u} n) (hc : c ∈ Ioo 0 b) :
    ContDiffAt ℝ ∞ D.cost (0, 0) := by
  have ha : ContDiffAt ℝ ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) => (lift (f (c, z.1))).2.val + z.2) (0, 0) :=
    (D.coordinate_smooth.comp (0, 0) contDiffAt_fst).add contDiffAt_snd
  have hP := D.prefixAction_contDiffAt hM12 hc D.center_mem
  have hS := D.tailAction_contDiffAt hM12 hc D.center_mem
  have hP' : ContDiffAt ℝ ∞ D.prefixAction (0, (lift (f (c, 0))).2.val + 0) := by
    simpa only [add_zero] using hP
  have hS' : ContDiffAt ℝ ∞ D.tailAction ((lift (f (c, 0))).2.val + 0) := by
    simpa only [add_zero] using hS
  have hPcomp := hP'.comp (0, 0) (contDiffAt_fst.prodMk ha)
  have hScomp := hS'.comp (0, 0) ha
  exact hPcomp.add hScomp

end GaugeEndpointFamily

end PoincareMT.M14
