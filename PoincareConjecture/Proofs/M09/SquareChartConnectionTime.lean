import PoincareConjecture.Proofs.M09.SquareChartRicciTime
import PoincareConjecture.Proofs.M09.SquareChartCurvature
import PoincareConjecture.Proofs.M09.CoordinateConnectionTime
import PoincareConjecture.Proofs.M09.CoordinateCompatibility

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option backward.isDefEq.respectTransparency false in
theorem squareChartConnection_time_at_center {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u})
    (T b : ℝ) (hb : 0 < b) (hwindow : Set.Icc (T - b) T ⊆ J)
    (p : M) (s : ℝ) (hs : s ∈ Set.Ioo (-Real.sqrt b) (Real.sqrt b)) (U V W : E) :
    squareChartMetric F T p (s, (chartAt E p) p)
      (fderiv ℝ (coordinateConnectionBilinear (squareChartMetric F T p))
        (s, (chartAt E p) p) (1, 0) U V) W =
      2 * s * backwardConnectionVariationPairing (F.connection (T - s ^ 2)) p U V W := by
  let Ω := Set.Ioo (-Real.sqrt b) (Real.sqrt b) ×ˢ (chartAt E p).target
  have hΩ : IsOpen Ω := isOpen_Ioo.prod (chartAt E p).open_target
  have hz : (s, (chartAt E p) p) ∈ Ω :=
    ⟨hs, (chartAt E p).map_source (mem_chart_source E p)⟩
  have hG := squareChartMetric_smooth F T b hb hwindow p
  have h := coordinateConnection_time_pairing (squareChartMetric F T p) Ω hΩ hG
    (fun z hz a ha ↦ squareChartMetric_pos F T p z hz.2 a ha)
    s ((chartAt E p) p) hz U V W
  dsimp only at h
  rw [squareChartMetric_time_space_at_center F hM04 T b hb hwindow p s hs U V W,
    squareChartMetric_time_space_at_center F hM04 T b hb hwindow p s hs V U W,
    squareChartMetric_time_space_at_center F hM04 T b hb hwindow p s hs W U V,
    squareChartMetric_time_at_center F T b hb hwindow p s hs,
    coordinateConnectionBilinear_apply] at h
  have hsym (a c : E) :
      coordinateConnection (squareChartMetric F T p) (s, (chartAt E p) p) a c =
        coordinateConnection (squareChartMetric F T p) (s, (chartAt E p) p) c a :=
    coordinateConnection_symm (squareChartMetric F T p) (s, (chartAt E p) p)
      ((hG.contDiffAt (hΩ.mem_nhds hz)).differentiableAt (by simp))
      (Filter.Eventually.of_forall (fun z a c ↦ squareChartMetric_symm F T p z a c)) a c
  have hRicSym (a c : E) :
      (F.connection (T - s ^ 2)).ricci p a c =
        (F.connection (T - s ^ 2)).ricci p c a :=
    ((hM04.tensor_calculus n M (F.metric (T - s ^ 2)) (F.connection (T - s ^ 2))).2.2.2.1
      p a c 0 0).2.2.2
  rw [h, backwardConnectionVariationPairing,
    ricciDerivativePairing_centeredCoordinates hM04 (F.connection (T - s ^ 2)) p U V W,
    ricciDerivativePairing_centeredCoordinates hM04 (F.connection (T - s ^ 2)) p V U W,
    ricciDerivativePairing_centeredCoordinates hM04 (F.connection (T - s ^ 2)) p W U V]
  simp only [← squareChartConnection_at_center F T b hb hwindow p s hs]
  rw [hsym V U, hsym W U, hsym W V,
    hRicSym (coordinateConnection (squareChartMetric F T p) (s, (chartAt E p) p) U W) V]
  ring

end PoincareConjecture.Proofs.M09
