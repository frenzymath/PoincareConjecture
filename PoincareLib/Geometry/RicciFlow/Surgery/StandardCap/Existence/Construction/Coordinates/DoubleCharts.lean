import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Metric.DoubleMetric
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Basic.OpenInclusionDifferential
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Limits.CompactCompleteness
import PoincareLib.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.QuotientCoefficients

/-!
# Fixed original-cap coordinates on each compact double

Morgan-Tian Theorem 12.5, p. 297. The canonical quotient parametrizations
are defined on the literal open subsets of the original R3. They preserve
the supplied metric exactly there and cover the double. These are fixed
initial exhaustion maps, before any evolving flow or limit is selected.
-/

set_option autoImplicit false

open Set Topology Poincare.Gluing
open scoped Manifold ContDiff

namespace PoincareMT.M34

variable {g : RiemannianMetric 3 StandardCapSpace}

/-- The fixed parametrization of a double piece by the original cap
(Theorem 12.5 compact-double construction, p. 297). -/
noncomputable def endDoubleParametrization (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) (i : Bool) : StandardCapSpace → EndDouble e hL := by
  let := endDoublePiece_nonempty e hL
  exact ChartDistance.chartParametrization (fun _ : Bool => endTruncation e (L + 1))
    (fun _ => endTruncation_isOpen e (show 0 ≤ L + 1 by linarith))
    (i := i) ((endDoubleOverlap e hL).include i)

/-- On its original open domain the parametrization is the quotient inclusion
(Theorem 12.5 compact-double construction, p. 297). -/
theorem endDoubleParametrization_apply (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) (i : Bool) (x : EndDoublePiece e L) :
    endDoubleParametrization e hL i (x : StandardCapSpace) =
      (endDoubleOverlap e hL).include i x := by
  let := endDoublePiece_nonempty e hL
  exact ChartDistance.chartParametrization_apply
    (fun _ : Bool => endTruncation e (L + 1))
    (fun _ => endTruncation_isOpen e (show 0 ≤ L + 1 by linarith))
    (i := i) ((endDoubleOverlap e hL).include i) x

/-- The fixed cap parametrization is smooth on the exact truncation domain
(Theorem 12.5 compact-double construction, p. 297). -/
theorem endDoubleParametrization_contMDiffOn (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) (i : Bool) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (endDoubleParametrization e hL i)
      (endTruncation e (L + 1)) := by
  let := endDoublePiece_nonempty e hL
  let := endDoublePieceChartedSpace e hL
  exact ChartDistance.contMDiffOn_chartParametrization
    (fun _ : Bool => endTruncation e (L + 1))
    (fun _ => endTruncation_isOpen e (show 0 ≤ L + 1 by linarith))
    (i := i)
    (endDouble_include_isLocalDiffeomorph e hL i).contMDiff

/-- Parametrization and piece inclusion have the same derivative in
canonical inclusion coordinates (Theorem 12.5, p. 297). -/
theorem endDoubleParametrization_mfderiv (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) (i : Bool) :
    let := endDoublePieceChartedSpace e hL
    ∀ x : EndDoublePiece e L,
      mfderiv (𝓡 3) (𝓡 3) (endDoubleParametrization e hL i) (x : StandardCapSpace) =
        mfderiv (𝓡 3) (𝓡 3) ((endDoubleOverlap e hL).include i) x := by
  let := endDoublePiece_nonempty e hL
  let := endDoublePieceChartedSpace e hL
  dsimp only
  intro x
  exact ChartDistance.mfderiv_chartParametrization
    (fun _ : Bool => endTruncation e (L + 1))
    (fun _ => endTruncation_isOpen e (show 0 ≤ L + 1 by linarith)) (i := i) x
    ((endDouble_include_isLocalDiffeomorph e hL i).contMDiff x)

set_option backward.isDefEq.respectTransparency false in
/-- The initial metric is exactly preserved in fixed original-cap coordinates
(Theorem 12.5 compact-double construction, p. 297). -/
theorem endDoubleParametrization_metric (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) (i : Bool) {x : StandardCapSpace}
    (hx : x ∈ endTruncation e (L + 1)) (u v : TangentSpace (𝓡 3) x) :
    g.inner x u v = (endDoubleMetric e hL).inner (endDoubleParametrization e hL i x)
      (mfderiv (𝓡 3) (𝓡 3) (endDoubleParametrization e hL i) x u)
      (mfderiv (𝓡 3) (𝓡 3) (endDoubleParametrization e hL i) x v) := by
  let := endDoublePiece_nonempty e hL
  let := endDoublePieceChartedSpace e hL
  let := endDoublePiece_isManifold e hL
  let p : EndDoublePiece e L := ⟨x, hx⟩
  have hp := endDoubleMetric_preserves e hL i p u v
  rw [mfderiv_subtypeVal_singleton
    (endTruncation_isOpen e (show 0 ≤ L + 1 by linarith)) p] at hp
  change g.inner x u v = _ at hp
  rw [show x = (p : StandardCapSpace) from rfl,
    endDoubleParametrization_apply, endDoubleParametrization_mfderiv]
  exact hp

/-- Every point of the double is represented by one of the two fixed
cap parametrizations (Theorem 12.5 compact-double construction, p. 297). -/
theorem endDoubleParametrization_cover (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) (q : EndDouble e hL) :
    ∃ (i : Bool) (x : StandardCapSpace), x ∈ endTruncation e (L + 1) ∧
      endDoubleParametrization e hL i x = q := by
  induction q using Quotient.inductionOn with
  | h a =>
    rcases a with ⟨i, x⟩
    exact ⟨i, x, x.property, endDoubleParametrization_apply e hL i x⟩

/-- The constructed double is complete for its actual Riemannian metric
(Theorem 12.5 compact-double construction, p. 297). -/
theorem endDoubleMetric_complete (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) : MetricComplete (endDoubleMetric e hL) :=
  (endDoubleMetric e hL).metricComplete_of_compact

end PoincareMT.M34
