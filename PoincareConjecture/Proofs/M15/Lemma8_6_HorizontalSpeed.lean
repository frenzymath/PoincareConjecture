import PoincareConjecture.Proofs.M04.TensorNormBounds
import PoincareConjecture.Proofs.M15.Lemma8_6_HorizontalEnergy
import PoincareConjecture.Proofs.M15.Mathlib.WeightedSpeed










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M15

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}



theorem abs_horizontalRicci_le_curvatureNorm
    (p : G.Point) (v : G.Horizontal p) :
    |horizontalRicci G.leafwise p v v| ≤
      (n : ℝ) * horizontalCurvatureNorm G.leafwise p *
        G.spacetime.horizontalMetric.inner p v v := by
  let t := G.spacetime.timeFunction p
  let x := spacetimeSlicePoint G.slices p
  let w := ((G.slices t).tangentEquiv x).symm v
  have h := M04.abs_ricci_le_curvatureTensorNorm
    (G.leafwise.sliceConnection t) x w
  have hmetric : (G.slices t).metricOnPoints.inner x w w =
      G.spacetime.horizontalMetric.inner p v v := by
    exact ((G.slices t).metric_eq x w w).trans
      (congrArg₂ (fun a b : G.Horizontal p => G.spacetime.horizontalMetric.inner p a b)
        (((G.slices t).tangentEquiv x).apply_symm_apply v)
        (((G.slices t).tangentEquiv x).apply_symm_apply v))
  change |horizontalRicci G.leafwise p v v| ≤
    (n : ℝ) * horizontalCurvatureNorm G.leafwise p *
      (G.slices t).metricOnPoints.inner x w w at h
  rwa [hmetric] at h



theorem squareRootPath_speed_le
    (D : SpacetimeHorizontalConnection G.leafwise)
    {T tau : ℝ} {x y : G.Point} {p : M14BackwardPath G T 0 tau x y}
    (R : M14SquareRootPath G p)
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval 0 tau)
      R.horizontal_velocity)
    {S a b : ℝ} (hS : 0 ≤ S) (hStau : S ≤ Real.sqrt tau)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hEuler : ∀ s ∈ Set.Ioo 0 S,
      M14SquareRootEulerResidual G R E s (R.horizontal_velocity s) = 0)
    (hRicci : ∀ s ∈ Set.Ioo 0 S,
      |horizontalRicci G.leafwise (R.curve s)
        (R.horizontal_velocity s) (R.horizontal_velocity s)| ≤
      a * G.spacetime.horizontalMetric.inner (R.curve s)
        (R.horizontal_velocity s) (R.horizontal_velocity s))
    (hScalar : ∀ s ∈ Set.Ioo 0 S,
      |M14HorizontalScalarDifferential G (R.curve s) (R.horizontal_velocity s).val| ≤
      b * Real.sqrt (G.spacetime.horizontalMetric.inner (R.curve s)
        (R.horizontal_velocity s) (R.horizontal_velocity s))) :
    ∀ s ∈ Set.Icc 0 S,
      Real.sqrt (G.spacetime.horizontalMetric.inner (R.curve s)
        (R.horizontal_velocity s) (R.horizontal_velocity s)) ≤
      Real.exp (a * s ^ 2) *
        (Real.sqrt (G.spacetime.horizontalMetric.inner (R.curve 0)
          (R.horizontal_velocity 0) (R.horizontal_velocity 0)) +
          (2 / 3 : ℝ) * b * s ^ 3) := by
  let q := fun s => G.spacetime.horizontalMetric.inner (R.curve s)
    (R.horizontal_velocity s) (R.horizontal_velocity s)
  let q' := fun s =>
    4 * s ^ 2 * M14HorizontalScalarDifferential G (R.curve s)
        (R.horizontal_velocity s).val -
      4 * s * horizontalRicci G.leafwise (R.curve s)
        (R.horizontal_velocity s) (R.horizontal_velocity s)
  have hsubset : Icc 0 S ⊆ M14SqrtParameterInterval 0 tau := by
    intro s hs
    exact ⟨by simpa only [Real.sqrt_zero] using hs.1, hs.2.trans hStau⟩
  have hq : ContinuousOn q (Icc 0 S) :=
    (horizontal_energy_continuousOn E
      (R.smooth.continuousOn.mono R.interval_subset)).mono hsubset
  have hq_nonneg (s : ℝ) (_hs : s ∈ Icc 0 S) : 0 ≤ q s := by
    by_cases hz : R.horizontal_velocity s = 0
    · simp [q, hz]
    · exact (G.spacetime.horizontalMetric.pos _ _ hz).le
  have hq' (s : ℝ) (hs : s ∈ Ioo 0 S) : HasDerivAt q (q' s) s :=
    hasDerivAt_square_energy D R E
      ⟨by simpa only [Real.sqrt_zero] using hs.1, hs.2.trans_le hStau⟩ (hEuler s hs)
  have hbound (s : ℝ) (hs : s ∈ Ioo 0 S) :
      q' s ≤ 4 * a * s * q s + 4 * b * s ^ 2 * Real.sqrt (q s) := by
    have hR := (neg_le_abs
      (horizontalRicci G.leafwise (R.curve s)
        (R.horizontal_velocity s) (R.horizontal_velocity s))).trans (hRicci s hs)
    have hV := (le_abs_self
      (M14HorizontalScalarDifferential G (R.curve s)
        (R.horizontal_velocity s).val)).trans (hScalar s hs)
    have hR' := mul_le_mul_of_nonneg_left hR
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hs.1.le)
    have hV' := mul_le_mul_of_nonneg_left hV (by positivity : 0 ≤ 4 * s ^ 2)
    dsimp only [q', q]
    nlinarith only [hR', hV']
  exact Real.sqrt_le_exp_sq_mul_of_deriv_le ha hb hS hq hq_nonneg hq' hbound

end PoincareConjecture.Proofs.M15
