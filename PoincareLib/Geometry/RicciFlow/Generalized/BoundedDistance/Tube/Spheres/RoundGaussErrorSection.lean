import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Spheres.RoundMetricDerivatives
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# A smooth coordinate section of the actual round metric error

The normalized source-minus-model coefficients are smooth on the domain of
any smooth model chart. A compact cutoff produces a global smooth bilinear
field agreeing with those coefficients near the chart centre. Its tensor
evaluation is smooth on arbitrary smooth Euclidean sections, so it can be
used in M07's covariant pullback naturality theorem. No source curvature or
ordinary metric-jet comparison is assumed here.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter Metric
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M28.tube

open PoincareMT.SpacetimeBounds

private abbrev GaussE := EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

/-- Both metrics are written in the same actual model parametrization. -/
def roundGaussErrorCoefficients
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) (e : GaussE → N.model.carrier) :
    GaussE → MetricCoefficient 3 :=
  fun y => N.scale • g.pullbackCoefficients (N.forward ∘ e) y -
    N.model_metric.pullbackCoefficients e y

theorem contDiffOn_roundGaussErrorCoefficients
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {e : GaussE → N.model.carrier} {U : Set GaussE} (hU : IsOpen U)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e U) :
    ContDiffOn ℝ ∞ (roundGaussErrorCoefficients N e) U := by
  intro y hy
  have he' := he.contMDiffAt (hU.mem_nhds hy)
  have hf := (N.forward_smooth (e y)).comp y he'
  exact ((g.contDiffAt_pullbackCoefficients hf).const_smul N.scale).sub
    (N.model_metric.contDiffAt_pullbackCoefficients he') |>.contDiffWithinAt

theorem roundGaussErrorCoefficients_apply
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {e : GaussE → N.model.carrier} {y : GaussE}
    (he : ContMDiffAt (𝓡 3) (𝓡 3) ∞ e y) (v : Fin 2 → GaussE) :
    roundGaussErrorCoefficients N e y (v 0) (v 1) =
      roundMetricError N (e y)
        (fun i => mfderiv (𝓡 3) (𝓡 3) e y (v i)) := by
  have hderiv := mfderiv_comp y
    ((N.forward_smooth (e y)).mdifferentiableAt (by simp))
    (he.mdifferentiableAt (by simp))
  simp only [roundGaussErrorCoefficients, roundMetricError,
    RiemannianMetric.pullbackCoefficients, singularMetricPullback,
    hderiv, sub_apply, smul_apply, smul_eq_mul]
  rfl

private theorem smooth_bilinear_tensor
    {B : GaussE → MetricCoefficient 3} (hB : ContDiff ℝ ∞ B) :
    IsSmoothCovariantTensor
      (fun (y : GaussE) (v : Fin 2 → TangentSpace (𝓡 3) y) =>
        B y (v 0) (v 1)) := by
  constructor
  · intro y
    let A : MultilinearMap ℝ
        (fun _ : Fin 2 => TangentSpace (𝓡 3) y) ℝ :=
      MultilinearMap.mk' (fun v => B y (v 0) (v 1))
        (by intro v i a b; fin_cases i <;> simp [map_add])
        (by intro v i c a; fin_cases i <;> simp [map_smul])
    exact ⟨A, fun _ => rfl⟩
  · intro U hU X hX y hy
    have hXi (i : Fin 2) : ContDiffAt ℝ ∞ (X i) y := by
      have h := (Bundle.contMDiffAt_totalSpace.mp
        ((hX i).contMDiffAt (hU.mem_nhds hy))).2
      simpa using contMDiffAt_iff_contDiffAt.mp h
    exact (contMDiffAt_iff_contDiffAt.mpr
      ((hB.contDiffAt.clm_apply (hXi 0)).clm_apply (hXi 1))).contMDiffWithinAt

/-- A compactly supported smooth bilinear section realizes the actual
normalized metric error on a prescribed smaller ball and as a germ at zero.
This needs only chart smoothness; Gauss normalization and invertibility will
be used by subsequent derivative estimates. -/
theorem exists_round_gauss_error_section
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {r s R : ℝ} (hr : 0 < r) (hrs : r < s) (hsR : s < R)
    (e : GaussE → N.model.carrier)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e (ball 0 R)) :
    ∃ B : GaussE → MetricCoefficient 3,
      ContDiff ℝ ∞ B ∧ HasCompactSupport B ∧
      IsSmoothCovariantTensor
        (fun (y : GaussE) (v : Fin 2 → TangentSpace (𝓡 3) y) =>
          B y (v 0) (v 1)) ∧
      (∀ y ∈ closedBall (0 : GaussE) r,
        B y = roundGaussErrorCoefficients N e y) ∧
      (∀ y ∈ ball (0 : GaussE) r, ∀ v : Fin 2 → GaussE,
        B y (v 0) (v 1) = roundMetricError N (e y)
          (fun i => mfderiv (𝓡 3) (𝓡 3) e y (v i))) ∧
      (∀ᶠ y in 𝓝 (0 : GaussE), ∀ v : Fin 2 → GaussE,
        B y (v 0) (v 1) = roundMetricError N (e y)
          (fun i => mfderiv (𝓡 3) (𝓡 3) e y (v i))) := by
  let f : ContDiffBump (0 : GaussE) := ⟨r, s, hr, hrs⟩
  let B : GaussE → MetricCoefficient 3 :=
    fun y => f y • roundGaussErrorCoefficients N e y
  have hraw := contDiffOn_roundGaussErrorCoefficients N isOpen_ball he
  have hsupport (y : GaussE) (hy : y ∈ tsupport f) : y ∈ ball (0 : GaussE) R := by
    rw [f.tsupport_eq] at hy
    exact lt_of_le_of_lt hy hsR
  have hB : ContDiff ℝ ∞ B := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ tsupport f
    · exact f.contDiff.contDiffAt.smul
        (hraw.contDiffAt (isOpen_ball.mem_nhds (hsupport y hy)))
    · apply (contDiffAt_const (c := (0 : MetricCoefficient 3))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
      simp [B, hz]
  have hcompact : HasCompactSupport B := f.hasCompactSupport.smul_right
  have heq (y : GaussE) (hy : y ∈ closedBall (0 : GaussE) r) :
      B y = roundGaussErrorCoefficients N e y := by
    simp only [B, f.one_of_mem_closedBall hy, one_smul]
  have herror (y : GaussE) (hy : y ∈ ball (0 : GaussE) r) (v : Fin 2 → GaussE) :
      B y (v 0) (v 1) = roundMetricError N (e y)
        (fun i => mfderiv (𝓡 3) (𝓡 3) e y (v i)) := by
    rw [heq y (ball_subset_closedBall hy)]
    exact roundGaussErrorCoefficients_apply N
      (he.contMDiffAt (isOpen_ball.mem_nhds
        (ball_subset_ball (hrs.trans hsR).le hy))) v
  refine ⟨B, hB, hcompact, smooth_bilinear_tensor hB, heq, herror, ?_⟩
  exact Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self hr)) herror

end PoincareMT.M28.tube
