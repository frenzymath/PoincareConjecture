import PoincareConjecture.Proofs.M14.Sec6_7_ExponentialGram
import PoincareConjecture.Proofs.M14.Sec6_2_MovingMetric
import Mathlib.Analysis.Matrix.Normed










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Matrix.Norms.Elementwise

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}



theorem pullbackMetricPair_contDiffOn {T a b : ℝ} {x y : G.Point}
    {p : M14BackwardPath G T a b x y} (R : M14SquareRootPath G p)
    {Y Z : ∀ s, G.Horizontal (R.curve s)}
    (EY : M14PullbackExtension G R.curve (M14SqrtParameterInterval a b) Y)
    (EZ : M14PullbackExtension G R.curve (M14SqrtParameterInterval a b) Z) :
    ContDiffOn ℝ ∞ (fun s => G.spacetime.horizontalMetric.inner (R.curve s) (Y s) (Z s))
      (M14SqrtParameterInterval a b) := by
  intro s hs
  have hR := R.smooth.mono R.interval_subset
  have hpair := pullbackExtensions_metric_pair_contMDiffAt EY EZ hs
  have h := hpair.comp_contMDiffWithinAt s (contMDiffWithinAt_id.prodMk (hR s hs))
  apply h.contDiffWithinAt.congr_of_mem _ hs
  intro r hr
  dsimp only [Function.comp_def, id_eq]
  rw [EY.agrees r hr, EZ.agrees r hr]

variable {T : ℝ} {x : G.Point}



theorem exponentialGram_contDiffOn
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (v : Fin n → G.Horizontal x)
    {Z : G.Horizontal x} {b : ℝ} (hb : (Z, b) ∈ E.domain) (hpos : 0 < b) :
    ContDiffOn ℝ ∞ (exponentialGram E v Z) (Icc 0 b) := by
  let P := exponentialInitialValuePath E Z b hb hpos
  let Q := fun i => initialValuePath_differentialData hM04 hM12 P (v i)
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  have h := pullbackMetricPair_contDiffOn P.square_path (Q i).extension (Q j).extension
  have hC : M14SqrtParameterInterval 0 (b ^ 2) = Icc 0 b := by
    simp only [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hpos.le]
  have hsub : Icc 0 b ⊆ M14SqrtParameterInterval 0 (b ^ 2) := by rw [hC]
  apply (h.mono hsub).congr
  intro s hs
  exact exponentialGram_eq_jacobi_pair hM04 hM12 E v hb hpos (hC.symm ▸ hs) i j



theorem exponentialJacobian_continuousOn
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (v : Fin n → G.Horizontal x)
    {Z : G.Horizontal x} {b : ℝ} (hb : (Z, b) ∈ E.domain) (hpos : 0 < b) :
    ContinuousOn (exponentialJacobian E v Z) (Icc 0 b) := by
  have h := (exponentialGram_contDiffOn hM04 hM12 E v hb hpos).continuousOn
  have hc : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => Real.sqrt (max 0 A.det)) :=
    Real.continuous_sqrt.comp (continuous_const.max continuous_id.matrix_det)
  exact hc.comp_continuousOn h

end PoincareConjecture.M14
