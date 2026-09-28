import PoincareConjecture.Proofs.M34.Thm12_5_Existence.DoubleTopology
import PoincareConjecture.Proofs.M34.Mathlib.OpenSubsetTransitionSmooth
import PoincareConjecture.Proofs.M07.Geometry.Manifold.Gluing.Smooth
import PoincareConjecture.Proofs.M07.Geometry.Manifold.LocalDiffeomorph










set_option autoImplicit false

open Set Topology Poincare.Gluing
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

variable {g : RiemannianMetric 3 StandardCapSpace}



noncomputable abbrev endDoublePieceChartedSpace (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) : ChartedSpace StandardCapSpace (EndDoublePiece e L) := by
  let := endDoublePiece_nonempty e hL
  have hU := endTruncation_isOpen e (show 0 ≤ L + 1 by linarith)
  exact hU.isOpenEmbedding_subtypeVal.singletonChartedSpace



theorem endDoublePiece_isManifold (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) :
    let := endDoublePieceChartedSpace e hL
    IsManifold (𝓡 3) ∞ (EndDoublePiece e L) := by
  let := endDoublePiece_nonempty e hL
  have hU := endTruncation_isOpen e (show 0 ≤ L + 1 by linarith)
  exact hU.isOpenEmbedding_subtypeVal.isManifold_singleton



theorem endDoublePiece_subtypeVal_isLocalDiffeomorph (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) :
    let := endDoublePieceChartedSpace e hL
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (Subtype.val : EndDoublePiece e L → StandardCapSpace) := by
  let := endDoublePiece_nonempty e hL
  exact Poincare.isLocalDiffeomorph_subtypeVal (𝓡 3) _
    (endTruncation_isOpen e (show 0 ≤ L + 1 by linarith)) ∞



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



noncomputable instance endDouble_chartedSpace (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) : ChartedSpace StandardCapSpace (EndDouble e hL) := by
  let := endDoublePiece_nonempty e hL
  exact quotientChartedSpace (fun _ : Bool => endTruncation e (L + 1))
    (fun _ => endTruncation_isOpen e (show 0 ≤ L + 1 by linarith)) (endDoubleOverlap e hL)



instance endDouble_isManifold (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) : IsManifold (𝓡 3) ∞ (EndDouble e hL) := by
  let := endDoublePiece_nonempty e hL
  exact quotient_isManifold (fun _ : Bool => endTruncation e (L + 1))
    (fun _ => endTruncation_isOpen e (show 0 ≤ L + 1 by linarith))
    (endDoubleOverlap e hL) (endDoubleOverlap_smooth e hL)



instance endDouble_nonempty (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) : Nonempty (EndDouble e hL) :=
  let x := Classical.choice (endDoublePiece_nonempty e hL)
  ⟨(endDoubleOverlap e hL).include false x⟩



theorem endDouble_include_isLocalDiffeomorph (e : StandardCylindricalEnd g)
    {L : ℝ} (hL : 1 < L) (i : Bool) :
    let := endDoublePieceChartedSpace e hL
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ ((endDoubleOverlap e hL).include i) := by
  let := endDoublePiece_nonempty e hL
  exact include_isLocalDiffeomorph (fun _ : Bool => endTruncation e (L + 1))
    (fun _ => endTruncation_isOpen e (show 0 ≤ L + 1 by linarith))
    (endDoubleOverlap e hL) (endDoubleOverlap_smooth e hL) i

end PoincareConjecture.M34
