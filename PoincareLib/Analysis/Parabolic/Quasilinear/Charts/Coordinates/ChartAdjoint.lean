/- Adapted from Mapher `PoincareMT/Proofs/M03/Existence/NativeChartAdjointNative.lean` at
f927d9e1f0810042766d3b5f64d3f4da02ee93cc. See
`references/ricci-flow/mapher/local-theory/port.json`. -/

import PoincareLib.Analysis.Parabolic.Quasilinear.Charts.Measure.ChartDensitySmooth
import PoincareLib.Analysis.Parabolic.Quasilinear.Euclidean.WeightedAdjoint
import PoincareLib.Analysis.Parabolic.Quasilinear.Localization.DirectionalProduct

/-!
# Native chart adjoints from the actual density

The local coefficients are the chart differential of the supplied smooth
field. The density is that of the constructed native finite chart measure.
Compact-test integration by parts and the actual scalar chain rule identify
the coordinate adjoint, including its zeroth-order divergence term.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter
open scoped Manifold ContDiff Topology SchwartzMap

noncomputable section

universe u

namespace PoincareMT.ChartMeasureNative.FiniteChartData

open TensorProbeNative EuclideanDerivativeNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

variable (d : FiniteChartData (n := n) (M := M))

/-- The divergence of the actual pushed-forward field in the native chart density. -/
def coordinateDivergence (p : M) (V : SmoothField (n := n) (M := M)) (z : E) : ℝ :=
  densityDivergence (d.chartDensity p) (fun i z => chartField p V z i)
    (PiLp.basisFun 2 ℝ (Fin n)) z

/-- The actual weighted coordinate adjoint acting on scalar functions. -/
def coordinateAdjoint (p : M) (V : SmoothField (n := n) (M := M))
    (η : E → ℝ) (z : E) : ℝ :=
  densityAdjointTest (d.chartDensity p) (fun i z => chartField p V z i)
    (PiLp.basisFun 2 ℝ (Fin n)) η z

theorem coordinateDivergence_contDiffOn (p : M) (V : SmoothField (n := n) (M := M)) :
    ContDiffOn ℝ ∞ (d.coordinateDivergence p V) (chartAt E p).target :=
  densityDivergence_contDiffOn (chartAt E p).open_target
    (d.chartDensity_contDiffOn p) (fun _ hz => d.chartDensity_pos p hz)
    (contDiffOn_chartField_coordinate p V) _

theorem coordinateAdjoint_contDiffOn (p : M) (V : SmoothField (n := n) (M := M))
    {η : E → ℝ} (hη : ContDiffOn ℝ ∞ η (chartAt E p).target) :
    ContDiffOn ℝ ∞ (d.coordinateAdjoint p V η) (chartAt E p).target :=
  densityAdjointTest_contDiffOn (chartAt E p).open_target
    (d.chartDensity_contDiffOn p) (fun _ hz => d.chartDensity_pos p hz)
    (contDiffOn_chartField_coordinate p V) _ hη

theorem coordinateAdjoint_eq (p : M) (V : SmoothField (n := n) (M := M))
    {η : E → ℝ} (hη : ContDiffOn ℝ ∞ η (chartAt E p).target)
    {z : E} (hz : z ∈ (chartAt E p).target) :
    d.coordinateAdjoint p V η z =
      -coefficientFirstOrder (fun i y => chartField p V y i)
        (PiLp.basisFun 2 ℝ (Fin n)) η z - d.coordinateDivergence p V z * η z :=
  densityAdjointTest_eq (chartAt E p).open_target
    (d.chartDensity_contDiffOn p) (fun _ hy => d.chartDensity_pos p hy)
    (contDiffOn_chartField_coordinate p V) _ hη hz

/-- The actual native weighted pairing in one chart. -/
theorem integral_coordinateFirstOrder_eq_adjoint (p : M)
    (V : SmoothField (n := n) (M := M)) (η : 𝓢(E, ℝ)) (hη : HasCompactSupport η)
    (hηU : tsupport η ⊆ (chartAt E p).target)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f (chartAt E p).target) :
    (∫ z, d.chartDensity p z *
      coefficientFirstOrder (fun i y => chartField p V y i)
        (PiLp.basisFun 2 ℝ (Fin n)) f z * η z) =
      ∫ z, d.chartDensity p z * f z * d.coordinateAdjoint p V η z :=
  integral_weightedFirstOrder_eq_adjoint η hη (chartAt E p).open_target hηU
    (d.chartDensity_contDiffOn p) (fun _ hz => d.chartDensity_pos p hz)
    (contDiffOn_chartField_coordinate p V) _ hf

/-- A supported coordinate coefficient gives a globally smooth native scalar. -/
theorem contMDiff_weight_mul_chart (p : M) {φ : M → ℝ}
    (hφ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ)
    (hφs : tsupport φ ⊆ (chartAt E p).source) {b : E → ℝ}
    (hb : ContDiffOn ℝ ∞ b (chartAt E p).target) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => φ x * b (chartAt E p x)) := by
  intro x
  by_cases hx : x ∈ (chartAt E p).source
  · have hlocal := hφ.contMDiffOn.mul (hb.contMDiffOn.comp
      (contMDiffOn_chart (I := 𝓡 n) (x := p)) (chartAt E p).mapsTo)
    exact hlocal.contMDiffAt ((chartAt E p).open_source.mem_nhds hx)
  · have hxφ : x ∉ tsupport φ := fun hs => hx (hφs hs)
    apply (contMDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxφ] with y hy
    change φ y = 0 at hy
    rw [hy, zero_mul]

/-- Partition-weighted local divergences produce an actual smooth global coefficient. -/
def fieldDivergence (V : SmoothField (n := n) (M := M)) (x : M) : ℝ :=
  ∑ i : d.centers, d.weight i x * d.coordinateDivergence i.val V (d.chart i x)

theorem fieldDivergence_contMDiff (V : SmoothField (n := n) (M := M)) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (d.fieldDivergence V) := by
  classical
  apply contMDiff_finsetSum
  intro i _
  exact contMDiff_weight_mul_chart i.val (d.weight_smooth i)
    (d.weight_support_subset i) (d.coordinateDivergence_contDiffOn i.val V)

theorem weight_mul_coordinateDivergence_contMDiff (i : d.centers)
    (V : SmoothField (n := n) (M := M)) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => d.weight i x * d.coordinateDivergence i.val V (d.chart i x)) :=
  contMDiff_weight_mul_chart i.val (d.weight_smooth i)
    (d.weight_support_subset i) (d.coordinateDivergence_contDiffOn i.val V)

/-- The native formal-adjoint expression; its global pairing is proved by the chart partition. -/
def fieldAdjoint (V : SmoothField (n := n) (M := M)) (f : M → ℝ) (x : M) : ℝ :=
  -scalarDirectional V f x - d.fieldDivergence V x * f x

theorem fieldAdjoint_contMDiff (V : SmoothField (n := n) (M := M))
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (d.fieldAdjoint V f) :=
  (contMDiff_directional hf V).neg.sub ((d.fieldDivergence_contMDiff V).mul hf)

theorem coordinateAdjoint_native (p : M) (V : SmoothField (n := n) (M := M))
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {z : E} (hz : z ∈ (chartAt E p).target) :
    d.coordinateAdjoint p V (f ∘ (chartAt E p).symm) z =
      -scalarDirectional V f ((chartAt E p).symm z) -
        d.coordinateDivergence p V z * f ((chartAt E p).symm z) := by
  rw [d.coordinateAdjoint_eq p V (contDiffOn_scalar_chartInverse p hf) hz]
  exact congrArg (fun a : ℝ => -a - d.coordinateDivergence p V z *
    f ((chartAt E p).symm z)) (directional_eq_chart_firstOrder p V hf hz).symm

/-- Coordinate integration by parts differentiates the supplied native scalar field. -/
theorem integral_nativeDirectional_chart_eq_adjoint (p : M)
    (V : SmoothField (n := n) (M := M)) (η : 𝓢(E, ℝ)) (hη : HasCompactSupport η)
    (hηU : tsupport η ⊆ (chartAt E p).target)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f) :
    (∫ z, d.chartDensity p z * scalarDirectional V f ((chartAt E p).symm z) * η z) =
      ∫ z, d.chartDensity p z * f ((chartAt E p).symm z) * d.coordinateAdjoint p V η z := by
  calc
    _ = ∫ z, d.chartDensity p z *
        coefficientFirstOrder (fun i y => chartField p V y i)
          (PiLp.basisFun 2 ℝ (Fin n)) (f ∘ (chartAt E p).symm) z * η z := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro z
      by_cases hz : z ∈ (chartAt E p).target
      · exact congrArg (fun a : ℝ => d.chartDensity p z * a * η z)
          (directional_eq_chart_firstOrder p V hf hz)
      · have hzero : η z = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hz (hηU hs))
        simp only [hzero, mul_zero]
    _ = _ := d.integral_coordinateFirstOrder_eq_adjoint p V η hη hηU
      (contDiffOn_scalar_chartInverse p hf)

end PoincareMT.ChartMeasureNative.FiniteChartData
