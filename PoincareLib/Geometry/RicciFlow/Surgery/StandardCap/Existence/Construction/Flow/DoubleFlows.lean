import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Flow.CommonCompactLifetime
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Curvature.DoubleCurvature
import PoincareLib.Geometry.RicciFlow.Local.Connection.Existence
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.ExistenceTheory

/-!
# Compact-double flows on one common closed time slab

The initial full-curvature bound is independent of the double height.
Compact existence, uniqueness, and continuation therefore give flows
on one positive closed time slab with one full-curvature bound. Their
initial metrics are the actual glued metrics, so the fixed cap charts
retain the prescribed initial geometry. This follows Morgan-Tian
Theorem 12.5, p. 297, with the reviewed full-energy comparison.
-/

set_option autoImplicit false

open scoped Manifold ContDiff
open Set

namespace PoincareMT.M34

/-- Compact Hausdorff doubles have the separation structure used by the
actual Riemannian completeness predicate (Theorem 12.5, p. 297). -/
instance endDouble_t3Space {g : RiemannianMetric 3 StandardCapSpace}
    (e : StandardCylindricalEnd g) {L : ℝ} (hL : 1 < L) : T3Space (EndDouble e hL) := by
  let := endDouble_t2Space e hL
  let := endDouble_compactSpace e hL
  let : R1Space (EndDouble e hL) := T2Space.r1Space
  let : T1Space (EndDouble e hL) := T2Space.t1Space
  let : NormalSpace (EndDouble e hL) := NormalSpace.of_compactSpace_r1Space
  let : T4Space (EndDouble e hL) := {}
  exact T4Space.t3Space

/-- All compact doubles have complete flows on one positive closed slab
with one full-curvature bound, selected before the height (Theorem 12.5, p. 297). -/
theorem exists_uniform_endDouble_flows (P : M34StandardCapPredecessors)
    (g0 : StandardInitialMetric) (E0 : StandardCapEstimate g0) :
    ∃ τ B : ℝ, 0 < τ ∧ 0 < B ∧ ∀ (L : ℝ) (hL : 1 < L),
      ∃ F : RicciFlow 3 (EndDouble g0.cylindrical_end hL) (Icc 0 τ),
        F.metric 0 = endDoubleMetric g0.cylindrical_end hL ∧
        (∀ t ∈ Icc 0 τ, MetricComplete (F.metric t)) ∧
        ∀ t ∈ Icc 0 τ, ∀ q : EndDouble g0.cylindrical_end hL,
          (F.connection t).curvatureTensorNorm q ≤ B := by
  obtain ⟨C, hC, hbound⟩ := endDouble_curvatureTensorNorm_bound g0 E0
  let τ : ℝ := 1 / (23328 * C)
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hsmall : 16 * (3 : ℝ) ^ 6 * C * τ ≤ 1 / 2 := by
    have hCne : C ≠ 0 := ne_of_gt hC
    dsimp [τ]
    norm_num
    field_simp
    nlinarith
  refine ⟨τ, 2 * C, hτ, by positivity, ?_⟩
  intro L hL
  obtain ⟨D⟩ := exists_leviCivitaData (endDoubleMetric g0.cylindrical_end hL)
  obtain ⟨F, hF, hnorm⟩ := exists_compactFlow_on_small_slab
    (P.local_flow 3 (EndDouble g0.cylindrical_end hL))
    (endDoubleMetric g0.cylindrical_end hL) D hC hτ hsmall (hbound L hL D)
  exact ⟨F, hF, fun t _ => (F.metric t).metricComplete_of_compact, hnorm⟩

end PoincareMT.M34
