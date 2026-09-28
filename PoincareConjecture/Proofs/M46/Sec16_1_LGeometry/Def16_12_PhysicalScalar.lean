import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Def16_12_IntrinsicComparison
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_TerminalScalar
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_ScalarScaling
import PoincareConjecture.Proofs.M36.StandardBalls

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

open SpacetimeBounds

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E" => StandardCapSpace

noncomputable local instance physicalScalarCoefficientNorm :
    NormedAddCommGroup (MetricCoefficient 3) := ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance physicalScalarCoefficientSpace :
    NormedSpace ℝ (MetricCoefficient 3) := ContinuousLinearMap.toNormedSpace

variable {F : SurgeryFlowData.{u}} {t : ℝ} {hT : t ∈ F.surgery_times}
  [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count} {A : ℝ}

noncomputable def capInitialPartialDiffeomorph
    (initial : SurgeryCapInitialComparison F t hT i A) :
    PartialDiffeomorph (𝓡 3) (𝓡 3) E (F.slice t).carrier ∞ where
  toFun := initial.chart
  invFun := initial.inverse
  source := F.standard_initial.metric.ball 0 A
  target := initial.chart '' F.standard_initial.metric.ball 0 A
  map_source' := fun _ hx => mem_image_of_mem initial.chart hx
  map_target' := by
    rintro _ ⟨x, hx, rfl⟩
    rw [initial.left_inverse hx]
    exact hx
  left_inv' := initial.left_inverse
  right_inv' := fun _ hx => initial.right_inverse (image_subset_range _ _ hx)
  open_source := by
    rw [M36.standard_ball_eq_euclidean F.standard_initial initial.A_pos]
    exact Metric.isOpen_ball
  open_target := Poincare.isOpen_image_of_smooth_leftInvOn (by
    rw [M36.standard_ball_eq_euclidean F.standard_initial initial.A_pos]
    exact Metric.isOpen_ball) initial.chart_smooth
      (initial.inverse_smooth.mono (image_subset_range _ _)) initial.left_inverse
  contMDiffOn_toFun := initial.chart_smooth
  contMDiffOn_invFun := initial.inverse_smooth.mono (image_subset_range _ _)

theorem jetScalar_normalizedPullback
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    {f : E → M} {U : Set E} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible)
    {Q : ℝ} (hQ : 0 < Q) {x : E} (hx : x ∈ U) :
    M44.jetScalarCurvature (metricTwoJet (fun y => Q • g.pullbackCoefficients f y) x) =
      D.scalarCurvature (f x) / Q := by
  let gQ := m01RescaledMetric g Q hQ
  let DQ := m01RescaledMetric_connection g D Q hQ
  have hcoeff : (fun y => Q • g.pullbackCoefficients f y) = gQ.pullbackCoefficients f := by
    funext y
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    rfl
  rw [hcoeff, M44.jetScalarCurvature_pullbackCoefficients gQ DQ hU hf hinv hx]
  exact M13.homothety_scalarCurvature_eq g gQ (Diffeomorph.refl (𝓡 3) M ∞)
    Q hQ (M44.rescaledMetric_identity_homothety hQ) D DQ (f x)

theorem capComparison_scalar_readout
    {S : MaximalStandardCapFlow F.standard_initial} {eta : ℝ}
    {J : Set ℝ} {U : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
    (hheight : 0 < F.parameters.h t) (s : ℝ) (hs : s ∈ J)
    {x : E} (hx : x ∈ F.standard_initial.metric.ball 0 A) :
    M44.jetScalarCurvature (metricTwoJet
      (capComparisonCoefficients e initial.chart s hs) x) =
      (F.parameters.h t) ^ 2 *
        (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
          (e.forward s hs (initial.chart x)) := by
  let f := capInitialPartialDiffeomorph initial
  have hV : IsOpen (F.standard_initial.metric.ball 0 A) := f.open_source
  have himage : initial.chart '' F.standard_initial.metric.ball 0 A = U :=
    comparison.choose_spec.2.2.2.1
  have hU : IsOpen U := himage ▸ f.open_target
  have hmap : MapsTo initial.chart (F.standard_initial.metric.ball 0 A) U := by
    intro y hy
    exact himage ▸ mem_image_of_mem initial.chart hy
  have hcomp : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (e.forward s hs ∘ initial.chart)
      (F.standard_initial.metric.ball 0 A) :=
    (e.forward_smooth s hs).comp initial.chart_smooth hmap
  have hinv (y : E) (hy : y ∈ F.standard_initial.metric.ball 0 A) :
      (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs ∘ initial.chart) y).IsInvertible :=
    M44.cylinder_chart_differential_invertible e hU f (by
      change initial.chart '' F.standard_initial.metric.ball 0 A ⊆ U
      rw [himage])
      s hs hy
  have heq : capComparisonCoefficients e initial.chart s hs =ᶠ[𝓝 x]
      (fun y => ((F.parameters.h t)⁻¹ ^ 2) •
        (F.metric (t + s / ((F.parameters.h t)⁻¹ ^ 2))).pullbackCoefficients
          (e.forward s hs ∘ initial.chart) y) := by
    filter_upwards [hV.mem_nhds hx] with y hy
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    exact (capComparisonCoefficients_apply e initial.chart s hs y v w).trans
      (M44.cylinderPhysicalCoefficients_normalization e hU hV initial.chart_smooth
        hmap s hs hy v w).symm
  have htwo := congrArg M44.jetScalarCurvature
    (show metricTwoJet (capComparisonCoefficients e initial.chart s hs) x =
      metricTwoJet (fun y => ((F.parameters.h t)⁻¹ ^ 2) •
        (F.metric (t + s / ((F.parameters.h t)⁻¹ ^ 2))).pullbackCoefficients
          (e.forward s hs ∘ initial.chart) y) x from by
      simp only [metricTwoJet, heq.eq_of_nhds, heq.fderiv_eq,
        (heq.fderiv (𝕜 := ℝ)).fderiv_eq])
  rw [htwo, jetScalar_normalizedPullback _
    (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))) hV hcomp hinv
    (sq_pos_of_pos (inv_pos.mpr hheight)) hx]
  simp only [div_inv_eq_mul, inv_pow, Function.comp_apply]
  ring

end PoincareConjecture.Proofs.M46
