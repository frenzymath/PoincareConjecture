import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Exponential.FamilySquareRegularization
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Action.IntrinsicEnergy
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Coordinates.CurvePhase
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Variation.Fields.SquareTimeFields

/-!
# Smooth energy of the actual square-time curve

Metric evaluation gives ambient smoothness. The constructed square-family
regularization gives its actual derivative throughout the closed interval.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.ReducedLength

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem regularizedCurveEnergy_contDiffOn {J : Set ℝ} (F : RicciFlow n M J)
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (α : ℝ → M) (U : Set ℝ) (hU : IsOpen U)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (htime : U ⊆ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) :
    ContDiffOn ℝ ∞ (regularizedCurveEnergy F T α) U := by
  have hbase := contMDiffOn_id.prodMk hα
  have hg := (squareTime_metric_smooth F T b hb hwindow).comp hbase
    (fun s hs ↦ ⟨htime hs, Set.mem_univ _⟩)
  have hphase := curvePhase_contMDiffOn α U hU hα
  have heval : ContMDiffOn (𝓘(ℝ, ℝ)) ((𝓡 n).prod (𝓘(ℝ, ℝ))) ∞
      (fun s : ℝ ↦ (⟨α s, regularizedCurveEnergy F T α s⟩ :
        Bundle.TotalSpace ℝ (Bundle.Trivial M ℝ))) U :=
    hg.clm_bundle_apply₂ hphase hphase
  have henergy : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ (regularizedCurveEnergy F T α) U := by
    intro s hs
    exact (Bundle.contMDiffWithinAt_totalSpace.mp (heval s hs)).2
  exact henergy.contDiffOn

theorem lExponentialFamily_squareEnergy_hasDerivAt {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τmax : ℝ}
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    {p : M} (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax)
    (s : ℝ) (hs : s ∈ Set.Icc 0 (Real.sqrt b)) :
    HasDerivAt (regularizedCurveEnergy F T (A.squareFamily Z))
      (4 * s ^ 2 * mvfderiv (𝓡 n) (F.connection (T - s ^ 2)).scalarCurvature
          (A.squareFamily Z s) (curveVelocity (A.squareFamily Z) s) -
        4 * s * (F.connection (T - s ^ 2)).ricci (A.squareFamily Z s)
          (curveVelocity (A.squareFamily Z) s) (curveVelocity (A.squareFamily Z) s)) s := by
  let R := lExponentialFamily_squareRegularization hM04 hτmax hwindow A Z b hb hmax
  have hsK : s ∈ sqrtParameterInterval 0 b := by
    simpa only [sqrtParameterInterval, Real.sqrt_zero] using hs
  have hK : UniqueDiffOn ℝ (sqrtParameterInterval 0 b) :=
    uniqueDiffOn_Icc (Real.sqrt_lt_sqrt (by norm_num) hb)
  have htime : s ∈ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) :=
    ⟨(neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le hs.1,
      hs.2.trans_lt (Real.sqrt_lt_sqrt hb.le hmax)⟩
  exact regularizedCurveEnergy_hasDerivAt F hM04 T τmax hτmax hwindow
    R.path.curve R.path.domain (sqrtParameterInterval 0 b) R.path.open_domain
    R.path.interval_subset hK R.path.smooth R.velocity_extension s hsK htime (R.equation s hsK)

end PoincareMT.ReducedLength
