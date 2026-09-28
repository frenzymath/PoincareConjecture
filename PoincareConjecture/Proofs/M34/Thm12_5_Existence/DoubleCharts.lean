import PoincareConjecture.Proofs.M34.Thm12_5_Existence.DoubleMetric
import PoincareConjecture.Proofs.M34.Mathlib.OpenInclusionDifferential
import PoincareConjecture.Proofs.M34.Standard.CompactCompleteness
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.QuotientCoefficients

set_option autoImplicit false

open Set Topology Poincare.Gluing
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace}

noncomputable def endDoubleParametrization (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) (i : Bool) : StandardCapSpace → EndDouble e hL := by
  let := endDoublePiece_nonempty e hL
  exact ChartDistance.chartParametrization (fun _ : Bool => endTruncation e (L + 1))
    (fun _ => endTruncation_isOpen e (show 0 ≤ L + 1 by linarith))
    (i := i) ((endDoubleOverlap e hL).include i)

theorem endDoubleParametrization_apply (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) (i : Bool) (x : EndDoublePiece e L) :
    endDoubleParametrization e hL i (x : StandardCapSpace) =
      (endDoubleOverlap e hL).include i x := by
  let := endDoublePiece_nonempty e hL
  exact ChartDistance.chartParametrization_apply
    (fun _ : Bool => endTruncation e (L + 1))
    (fun _ => endTruncation_isOpen e (show 0 ≤ L + 1 by linarith))
    (i := i) ((endDoubleOverlap e hL).include i) x

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

theorem endDoubleParametrization_cover (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) (q : EndDouble e hL) :
    ∃ (i : Bool) (x : StandardCapSpace), x ∈ endTruncation e (L + 1) ∧
      endDoubleParametrization e hL i x = q := by
  induction q using Quotient.inductionOn with
  | h a =>
    rcases a with ⟨i, x⟩
    exact ⟨i, x, x.property, endDoubleParametrization_apply e hL i x⟩

theorem endDoubleMetric_complete (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) : MetricComplete (endDoubleMetric e hL) :=
  (endDoubleMetric e hL).metricComplete_of_compact

end PoincareConjecture.M34
