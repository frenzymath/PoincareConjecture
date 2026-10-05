import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.SourceNames
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.Spheres.RoundTransfer
import PoincareLib.Geometry.RicciFlow.Rescaling.Construction

/-!
# Scalar readout in a common round-model parametrization

The actual model and normalized source metric two-jets have scalar values
six and the original source scalar divided by the component scale. The
parametrization is any smooth local map with invertible differential; no
atlas, Gauss identity or quantitative comparison is needed for the readout.
This supplies the scalar interpretation used in Morgan--Tian section 10.3.1,
printed p. 247. See the derivation in
`proof-work/tasks/M28/review-endpoints/2026-09-23-gauss-scalar-readout.md`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareMT.M28.tube

open PoincareMT.SpacetimeBounds

private abbrev ScalarReadoutE := EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- The smooth inverse in the frozen round certificate makes its actual
forward differential invertible. This is the local-coordinate input for
the scalar interpretation in section 10.3.1, printed p. 247. -/
theorem round_forward_mfderiv_isInvertible
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) (x : N.model.carrier) :
    (mfderiv (𝓡 3) (𝓡 3) N.forward x).IsInvertible := by
  have hopen : IsOpen N.carrier :=
    N.forward_image ▸ N.forward_openEmbedding.isOpen_range
  have hx : N.forward x ∈ N.carrier :=
    N.forward_image ▸ mem_range_self x
  have hcomp := mfderiv_comp x
    ((N.inverse_smooth.contMDiffAt (hopen.mem_nhds hx)).mdifferentiableAt
      (by simp))
    ((N.forward_smooth x).mdifferentiableAt (by simp))
  have hid : mfderiv (𝓡 3) (𝓡 3)
      (N.inverse ∘ N.forward) x =
      ContinuousLinearMap.id ℝ (TangentSpace (𝓡 3) x) := by
    rw [show N.inverse ∘ N.forward = id by
      funext y
      exact N.left_inverse y, mfderiv_id]
  rw [hid] at hcomp
  have hinj : Function.Injective (mfderiv (𝓡 3) (𝓡 3) N.forward x) := by
    intro v w hvw
    have hv := congrArg (fun L : TangentSpace (𝓡 3) x →L[ℝ]
        TangentSpace (𝓡 3) x => L v) hcomp
    have hw := congrArg (fun L : TangentSpace (𝓡 3) x →L[ℝ]
        TangentSpace (𝓡 3) x => L w) hcomp
    exact hv.trans ((congrArg
      (mfderiv (𝓡 3) (𝓡 3) N.inverse (N.forward x)) hvw).trans hw.symm)
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) x) := by
    unfold TangentSpace
    infer_instance
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) (N.forward x)) := by
    unfold TangentSpace
    infer_instance
  let : T2Space (TangentSpace (𝓡 3) x) :=
    FiberBundle.t2Space (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) x
  let : T2Space (TangentSpace (𝓡 3) (N.forward x)) :=
    FiberBundle.t2Space (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3)) (N.forward x)
  have hfin : Module.finrank ℝ (TangentSpace (𝓡 3) x) =
      Module.finrank ℝ (TangentSpace (𝓡 3) (N.forward x)) := by
    unfold TangentSpace
    rfl
  have hbij : Function.Bijective (mfderiv (𝓡 3) (𝓡 3) N.forward x) := by
    refine ⟨hinj, ?_⟩
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj
  exact ⟨(LinearEquiv.ofBijective
    (mfderiv (𝓡 3) (𝓡 3) N.forward x).toLinearMap hbij).toContinuousLinearEquiv, rfl⟩

/-- Any genuine local parametrization reads the curvature-one model scalar
as six, as used in section 10.3.1, printed p. 247. -/
theorem round_gauss_model_scalar_eq_six
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    {U : Set ScalarReadoutE} (hU : IsOpen U)
    {e : ScalarReadoutE → N.model.carrier}
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e U)
    (hi : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) e y).IsInvertible)
    {x : ScalarReadoutE} (hx : x ∈ U) :
    jetScalarCurvature (metricTwoJet (N.model_metric.pullbackCoefficients e) x) = 6 := by
  rw [jetScalarCurvature_metricTwoJet_pullback N.model_connection hU he hi hx]
  exact N.model_scalar_eq_six (e x)

/-- The metric scale in the frozen round comparison divides the actual
source scalar by that same positive scale. This is the common-chart scalar
readout for section 10.3.1, printed p. 247. -/
theorem round_gauss_source_scalar_eq
    [T2Space M]
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) (D : LeviCivitaData g)
    {U : Set ScalarReadoutE} (hU : IsOpen U)
    {e : ScalarReadoutE → N.model.carrier}
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e U)
    (hi : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) e y).IsInvertible)
    {x : ScalarReadoutE} (hx : x ∈ U) :
    jetScalarCurvature
        (metricTwoJet (fun y => N.scale •
          g.pullbackCoefficients (N.forward ∘ e) y) x) =
      D.scalarCurvature (N.forward (e x)) / N.scale := by
  have hsource : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (N.forward ∘ e) U :=
    N.forward_smooth.comp_contMDiffOn he
  have hsourceInv : ∀ y ∈ U,
      (mfderiv (𝓡 3) (𝓡 3) (N.forward ∘ e) y).IsInvertible := by
    intro y hy
    rw [mfderiv_comp y
      ((N.forward_smooth (e y)).mdifferentiableAt (by simp))
      ((he.contMDiffAt (hU.mem_nhds hy)).mdifferentiableAt (by simp))]
    exact (round_forward_mfderiv_isInvertible N (e y)).comp (hi y hy)
  let gs : RiemannianMetric 3 M :=
    M13.scaleSmoothMetric g N.scale N.scale_pos
  let Ds : LeviCivitaData gs :=
    M13.scaleLeviCivitaData D N.scale N.scale_pos
  have hcoeff : (fun y => N.scale • g.pullbackCoefficients (N.forward ∘ e) y) =
      gs.pullbackCoefficients (N.forward ∘ e) := by
    funext y
    ext v w
    rfl
  rw [hcoeff, jetScalarCurvature_metricTwoJet_pullback Ds hU hsource hsourceInv hx]
  have hscale := M13.homothety_scalarCurvature_eq g gs
    (Diffeomorph.refl (𝓡 3) M ∞) N.scale N.scale_pos
    (M13.identity_metricHomothety g N.scale N.scale_pos) D Ds (N.forward (e x))
  simpa only [Diffeomorph.coe_refl, id_eq, Function.comp_apply] using hscale

end PoincareMT.M28.tube
