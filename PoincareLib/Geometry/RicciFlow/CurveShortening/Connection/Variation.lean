import PoincareLib.Geometry.RicciFlow.CurveShortening.Connection.Curvature
import PoincareLib.Geometry.RicciFlow.Curvature.Evolution.Tensor.FlowTensorRegularity
import PoincareLib.Geometry.RicciFlow.Curvature.Evolution.Connection.ConnectionVariation

/-!
# Actual connection coefficients in real time

The actual spatial chart Christoffel coefficients are jointly smooth, and
their fixed-metric time pairing is the covariant Ricci variation. These
are the moving-connection inputs to the spatial form of MT2015Correction
Lemma 0.2, pp. 4-6. See `references/ricci-flow/mapher/curve-evolution/derivations/2026-09-20-moving-connection.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set Topology Filter
open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareMT.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

/-- Actual chart connection coefficients are jointly smooth through the
included time endpoints; MT2015Correction Lemma 0.2, pp. 4-6. -/
theorem flow_chartChristoffel_smooth [T2Space M]
    (F : RicciFlow n M J) (p : M) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
        RicciFlowAnalysis.shiChartChristoffel (F.connection z.1)
          (chartAt (EuclideanSpace ℝ (Fin n)) p) z.2)
      (J ×ˢ (chartAt (EuclideanSpace ℝ (Fin n)) p).target) := by
  let E := EuclideanSpace ℝ (Fin n)
  let : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
  let e := chartAt E p
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart
  have hi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart_symm
  rw [contDiffOn_clm_apply]
  intro u
  rw [contDiffOn_clm_apply]
  intro v
  apply (contDiffOn_piLp 2).mpr
  intro i
  let L : (z : ℝ × M) → TangentSpace (𝓡 n) z.2 →L[ℝ] ℝ := fun z =>
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).comp
      (mfderiv (𝓡 n) (𝓡 n) e z.2)
  have hL : ∀ (V : Set M), IsOpen V → V ⊆ e.source →
      ∀ (Z : (y : M) → TangentSpace (𝓡 n) y),
        ContMDiffOn (𝓡 n) (𝓡 n).tangent ∞ (T% Z) V →
        ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
          (fun z : ℝ × M => L z (Z z.2)) (J ×ˢ V) := by
    intro V hV hVU Z hZ
    have hs : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
        (fun z : ℝ × M => RicciFlowAnalysis.shiChartCoordinate e i z.2) (J ×ˢ V) :=
      ((RicciFlowAnalysis.shiChartCoordinate_smooth he i).mono hVU).comp contMDiffOn_snd
        (fun z hz => hz.2)
    apply (RicciFlowAnalysis.contMDiffOn_mvfderiv_spatial hV hs hZ).congr
    intro z hz
    change (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i)
      (mfderiv (𝓡 n) (𝓡 n) e z.2 (Z z.2)) =
      mvfderiv (𝓡 n) (RicciFlowAnalysis.shiChartCoordinate e i) z.2 (Z z.2)
    exact (RicciFlowAnalysis.shiChartCoordinate_derivative he (hVU hz.2) i (Z z.2)).symm
  have hconn := RicciFlowAnalysis.contMDiffOn_flow_linear_connection F e.open_source L hL
    (RicciFlowAnalysis.shiChartField_smooth he hi u) (RicciFlowAnalysis.shiChartField_smooth he hi v)
  have hparam : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ).prod (𝓡 n)) ∞
      (fun z : ℝ × E => (z.1, e.symm z.2)) (J ×ˢ e.target) :=
    contDiff_fst.contMDiff.contMDiffOn.prodMk
      (hi.comp contDiff_snd.contMDiff.contMDiffOn (fun z hz => hz.2))
  have hcomp := hconn.comp hparam (fun z hz => ⟨hz.1, e.map_target hz.2⟩)
  apply hcomp.contDiffOn.congr
  intro z hz
  change (RicciFlowAnalysis.shiChartChristoffel (F.connection z.1) e z.2 u v) i =
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i)
      (mfderiv (𝓡 n) (𝓡 n) e (e.symm z.2)
      ((F.connection z.1).connection (RicciFlowAnalysis.shiChartField e v) (e.symm z.2)
        (RicciFlowAnalysis.shiChartField e u (e.symm z.2))))
  rw [RicciFlowAnalysis.shiChartChristoffel_connection (F.connection z.1) he hi hz.2,
    ← RicciFlowAnalysis.shiChartField_at_inverse he hi hz.2]
  rfl

/-- Real-time differentiation of the actual connection, with the metric
and test fields fixed; MT2015Correction Lemma 0.2, pp. 4-6. -/
theorem hasDerivAt_flow_chartChristoffel_pair [T2Space M]
    (F : RicciFlow n M J) (p : M) {t : ℝ} {y : M}
    (ht : t ∈ interior J)
    (hy : y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (u v w : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt
      (fun r => (F.metric t).inner y
        (PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField p
          (RicciFlowAnalysis.shiChartChristoffel (F.connection r)
            (chartAt (EuclideanSpace ℝ (Fin n)) p)
            ((chartAt (EuclideanSpace ℝ (Fin n)) p) y) u v) y)
        (PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField p w y))
      (let X := PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField p u y;
       let Y := PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField p v y;
       let Z := PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField p w y;
       let D := F.connection t;
       -D.covariantTensorDerivative D.ricciEvaluation y ![X, Y, Z] -
         D.covariantTensorDerivative D.ricciEvaluation y ![Y, X, Z] +
         D.covariantTensorDerivative D.ricciEvaluation y ![Z, X, Y]) t := by
  let E := EuclideanSpace ℝ (Fin n)
  let e := chartAt E p
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart
  have hi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart_symm
  have hconn (r : ℝ) :
      PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField p
        (RicciFlowAnalysis.shiChartChristoffel (F.connection r) e (e y) u v) y =
      (F.connection r).connection (PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField p v) y
        (PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField p u y) := by
    apply ((mdifferentiable_chart (I := 𝓡 n) p).mfderiv hy).injective
    change mfderiv (𝓡 n) (𝓡 n) e y _ = mfderiv (𝓡 n) (𝓡 n) e y _
    erw [RicciFlowAnalysis.shiChartField_duality he hi hy]
    have h := RicciFlowAnalysis.shiChartChristoffel_connection (F.connection r) he hi
      (e.map_source hy) u v
    rw [← RicciFlowAnalysis.shiChartField_at_inverse he hi (e.map_source hy), e.left_inv hy] at h
    exact h
  have h := RicciFlowAnalysis.hasDerivAt_connection_pairing F e.open_source
    (PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField_smooth p u)
    (PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField_smooth p v)
    (PoincareMT.ReducedLengthMinimum.Variation.Geometry.chartVectorField_smooth p w) ht hy
  apply h.congr_of_eventuallyEq
  filter_upwards [] with r
  rw [hconn]

end PoincareMT.M62
