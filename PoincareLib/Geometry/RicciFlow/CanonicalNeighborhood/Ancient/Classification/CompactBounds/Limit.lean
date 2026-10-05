import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Escaping.Metric
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.Bounds

/-!
# Compact terminal limits of uniformly bounded slices

A uniform diameter bound on the source slices bounds all distances on the
actual terminal limit. Its completeness then gives compactness. This is the
compactness input for the quantitative compact-positive alternative.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace M23TerminalExtension

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}

/-- A uniform source distance bound passes to twice that bound on the
terminal limit, with no compactness assumption on that limit. -/
theorem terminal_edist_le_of_uniform_source_bound
    (T : M23TerminalExtension G) {D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ k (x y : (S.term k).carrier.carrier),
      (((S.term k).flow.flow.metric 0).edist x y).toReal ≤ D)
    (x y : G.limit.carrier.carrier) :
    (G.limit.flow.flow.metric 0).edist x y ≤ ENNReal.ofReal (2 * D) := by
  obtain ⟨e, hbase, _, hconv⟩ := T.terminal_embedding
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  obtain ⟨i, hi⟩ := mem_iUnion.mp (G.exhaustion_covers.symm ▸ mem_univ x)
  obtain ⟨j, hj⟩ := mem_iUnion.mp (G.exhaustion_covers.symm ▸ mem_univ y)
  obtain ⟨k, hk, hmetric⟩ := ((eventually_ge_atTop (max i j)).and
    (hconv.eventually_terminal_inverse_edist_bounds (fun k => (hbase k).2)
      (show 0 < D + 1 by linarith) (by norm_num : (1 : ℝ) < 2))).exists
  let E := (e k).spatialHomeomorph (mem_Iic.mpr le_rfl) (G.exhaustion_open k)
  have hx : x ∈ E.source := hmono ((le_max_left _ _).trans hk) hi
  have hy : y ∈ E.source := hmono ((le_max_right _ _).trans hk) hj
  have hball (z : (S.term (G.subsequence k)).carrier.carrier) :
      z ∈ ((S.term (G.subsequence k)).flow.flow.metric 0).ball
        (S.term (G.subsequence k)).base (D + 1) := by
    apply (ENNReal.lt_ofReal_iff_toReal_lt
      (((S.term (G.subsequence k)).flow.flow.metric 0).edist_ne_top _ _)).mpr
    exact (hbound _ _ _).trans_lt (by linarith)
  have hh := (hmetric (E x) (hball _) (E y) (hball _)).1
  change (G.limit.flow.flow.metric 0).edist (E.symm (E x)) (E.symm (E y)) ≤ _ at hh
  rw [E.left_inv hx, E.left_inv hy] at hh
  apply hh.trans
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  gcongr
  rw [← ENNReal.ofReal_toReal
    (((S.term (G.subsequence k)).flow.flow.metric 0).edist_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal (hbound _ _ _)

/-- Uniformly bounded terminal source diameters give a compact retained
terminal limit. -/
theorem isCompact_of_uniform_source_diameter
    (T : M23TerminalExtension G) {D : ℝ} (hD : 0 ≤ D)
    (hcompact : ∀ k, IsCompact (univ : Set (S.term k).carrier.carrier))
    (hdiam : ∀ k, metricDiameter ((S.term k).flow.flow.metric 0) univ ≤ D) :
    IsCompact (univ : Set G.limit.carrier.carrier) := by
  let g := G.limit.flow.flow.metric 0
  have hbound (k) (x y : (S.term k).carrier.carrier) :
      (((S.term k).flow.flow.metric 0).edist x y).toReal ≤ D :=
    (compact_toReal_edist_le_metricDiameter _ (hcompact k) x y).trans (hdiam k)
  have heq : {x | g.edist G.limit.base x ≤ ENNReal.ofReal (2 * D)} = univ :=
    eq_univ_of_forall (fun x => T.terminal_edist_le_of_uniform_source_bound hD hbound _ x)
  rw [← heq]
  exact g.isCompact_closedBall_of_metricComplete (G.limit.flow.complete 0 le_rfl) _ _

end M23TerminalExtension

end PoincareMT
