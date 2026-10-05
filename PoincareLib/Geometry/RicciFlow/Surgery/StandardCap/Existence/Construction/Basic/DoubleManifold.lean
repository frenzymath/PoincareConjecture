import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Basic.DoubleTopology
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Analysis.Basic.OpenSubsetTransitionSmooth
import PoincareLib.Geometry.Manifold.Gluing.Smooth
import PoincareLib.Geometry.Manifold.LocalDiffeomorph

/-!
# The smooth manifold structure of the compact double

Morgan-Tian Theorem 12.5, p. 297. The actual reflection transition is
smooth in the inclusion charts of the open truncations. M07's gluing
construction gives the quotient its Euclidean three-dimensional charts
and makes the two inclusions local diffeomorphisms.
-/

set_option autoImplicit false

open Set Topology Poincare.Gluing
open scoped Manifold ContDiff

namespace PoincareMT.M34

variable {g : RiemannianMetric 3 StandardCapSpace}

/-- Each open cap piece has the singleton chart given by inclusion in R3
(Theorem 12.5 compact-double construction, p. 297). -/
noncomputable abbrev endDoublePieceChartedSpace (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) : ChartedSpace StandardCapSpace (EndDoublePiece e L) := by
  let := endDoublePiece_nonempty e hL
  have hU := endTruncation_isOpen e (show 0 ≤ L + 1 by linarith)
  exact hU.isOpenEmbedding_subtypeVal.singletonChartedSpace

/-- The inclusion chart makes each piece a smooth manifold
(Theorem 12.5 compact-double construction, p. 297). -/
theorem endDoublePiece_isManifold (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) :
    let := endDoublePieceChartedSpace e hL
    IsManifold (𝓡 3) ∞ (EndDoublePiece e L) := by
  let := endDoublePiece_nonempty e hL
  have hU := endTruncation_isOpen e (show 0 ≤ L + 1 by linarith)
  exact hU.isOpenEmbedding_subtypeVal.isManifold_singleton

/-- The cap-piece inclusion is a local diffeomorphism for its actual chart
(Theorem 12.5 compact-double construction, p. 297). -/
theorem endDoublePiece_subtypeVal_isLocalDiffeomorph (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) :
    let := endDoublePieceChartedSpace e hL
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (Subtype.val : EndDoublePiece e L → StandardCapSpace) := by
  let := endDoublePiece_nonempty e hL
  exact Poincare.isLocalDiffeomorph_subtypeVal (𝓡 3) _
    (endTruncation_isOpen e (show 0 ≤ L + 1 by linarith)) ∞

/-- The restricted reflection is smooth on its exact overlap source
(Theorem 12.5 compact-double construction, p. 297). -/
theorem endDoubleTransition_contMDiffOn (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) :
    let := endDoublePieceChartedSpace e hL
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (endDoubleTransition e hL)
      (endDoubleTransition e hL).source := by
  let := endDoublePiece_nonempty e hL
  exact OpenPartialHomeomorph.contMDiffOn_onOpenSubset (𝓡 3)
    (endDoubleCollarHomeomorph e hL)
    (endTruncation_isOpen e (show 0 ≤ L + 1 by linarith))
    (endAxialReflection_collar_contMDiffOn e hL) (endDoubleCollar_subset_truncation e hL)

/-- All four transitions are smooth in the canonical inclusion charts
(Theorem 12.5 compact-double construction, p. 297). -/
theorem endDoubleOverlap_smooth (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) :
    let := endDoublePiece_nonempty e hL
    SmoothOverlap (fun _ : Bool => endTruncation e (L + 1))
      (fun _ => endTruncation_isOpen e (show 0 ≤ L + 1 by linarith))
      (endDoubleOverlap e hL) := by
  let := endDoublePiece_nonempty e hL
  let := endDoublePieceChartedSpace e hL
  dsimp only
  intro i j
  by_cases hij : i = j
  · subst j
    rw [(endDoubleOverlap e hL).self]
    exact contMDiff_id.contMDiffOn
  · rw [show (endDoubleOverlap e hL).transition i j = endDoubleTransition e hL from
      twoPieceOverlap_transition_ne _ _ hij]
    exact endDoubleTransition_contMDiffOn e hL

/-- The quotient receives the two inclusion charts constructed by gluing
(Theorem 12.5 compact-double construction, p. 297). -/
noncomputable instance endDouble_chartedSpace (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) : ChartedSpace StandardCapSpace (EndDouble e hL) := by
  let := endDoublePiece_nonempty e hL
  exact quotientChartedSpace (fun _ : Bool => endTruncation e (L + 1))
    (fun _ => endTruncation_isOpen e (show 0 ≤ L + 1 by linarith)) (endDoubleOverlap e hL)

/-- The compact double is a smooth three-dimensional manifold
(Theorem 12.5 compact-double construction, p. 297). -/
instance endDouble_isManifold (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) : IsManifold (𝓡 3) ∞ (EndDouble e hL) := by
  let := endDoublePiece_nonempty e hL
  exact quotient_isManifold (fun _ : Bool => endTruncation e (L + 1))
    (fun _ => endTruncation_isOpen e (show 0 ≤ L + 1 by linarith))
    (endDoubleOverlap e hL) (endDoubleOverlap_smooth e hL)

/-- A point in either piece supplies a point of the double
(Theorem 12.5 compact-double construction, p. 297). -/
instance endDouble_nonempty (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) : Nonempty (EndDouble e hL) :=
  let x := Classical.choice (endDoublePiece_nonempty e hL)
  ⟨(endDoubleOverlap e hL).include false x⟩

/-- Each cap piece includes into the double by a smooth local diffeomorphism
(Theorem 12.5 compact-double construction, p. 297). -/
theorem endDouble_include_isLocalDiffeomorph (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) (i : Bool) :
    let := endDoublePieceChartedSpace e hL
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ ((endDoubleOverlap e hL).include i) := by
  let := endDoublePiece_nonempty e hL
  exact include_isLocalDiffeomorph (fun _ : Bool => endTruncation e (L + 1))
    (fun _ => endTruncation_isOpen e (show 0 ≤ L + 1 by linarith))
    (endDoubleOverlap e hL) (endDoubleOverlap_smooth e hL) i

end PoincareMT.M34
