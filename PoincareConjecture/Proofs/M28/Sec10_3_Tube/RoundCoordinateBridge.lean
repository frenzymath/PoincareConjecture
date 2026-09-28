import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundTransfer
import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Coordinates.Coefficients
import PoincareConjecture.Proofs.M13.OrdinaryFlow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.M28.tube

open PoincareConjecture.SpacetimeBounds

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

noncomputable def roundSourceCoefficients
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) (q : N.model.carrier) :
    EuclideanSpace ℝ (Fin 3) → MetricCoefficient 3 :=
  fun p => N.scale • g.pullbackCoefficients
    (N.forward ∘ (extChartAt (𝓡 3) q).symm) p

noncomputable def roundModelCoefficients
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) (q : N.model.carrier) :
    EuclideanSpace ℝ (Fin 3) → MetricCoefficient 3 :=
  N.model_metric.pullbackCoefficients (extChartAt (𝓡 3) q).symm

noncomputable def roundSourceJet
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) (q : N.model.carrier)
    (p : EuclideanSpace ℝ (Fin 3)) : MetricTwoJet 3 :=
  metricTwoJet (roundSourceCoefficients N q) p

noncomputable def roundModelJet
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) (q : N.model.carrier)
    (p : EuclideanSpace ℝ (Fin 3)) : MetricTwoJet 3 :=
  metricTwoJet (roundModelCoefficients N q) p

theorem round_model_jet_invertible
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    (q : N.model.carrier) (p : EuclideanSpace ℝ (Fin 3))
    (hp : p ∈ (extChartAt (𝓡 3) q).target) :
    (roundModelJet N q p).1.IsInvertible := by
  change (N.model_metric.pullbackCoefficients
    (extChartAt (𝓡 3) q).symm p).IsInvertible
  exact N.model_metric.isInvertible_chartCoefficients q hp

private theorem round_forward_mfderiv_injective
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon) (x : N.model.carrier) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 3) N.forward x) := by
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
  intro v w hvw
  have hv := congrArg (fun L : TangentSpace (𝓡 3) x →L[ℝ]
      TangentSpace (𝓡 3) x => L v) hcomp
  have hw := congrArg (fun L : TangentSpace (𝓡 3) x →L[ℝ]
      TangentSpace (𝓡 3) x => L w) hcomp
  exact hv.trans ((congrArg
    (mfderiv (𝓡 3) (𝓡 3) N.inverse (N.forward x)) hvw).trans hw.symm)

theorem round_source_jet_invertible
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    (q : N.model.carrier) (p : EuclideanSpace ℝ (Fin 3))
    (hp : p ∈ (extChartAt (𝓡 3) q).target) :
    (roundSourceJet N q p).1.IsInvertible := by
  let c := extChartAt (𝓡 3) q
  let e : EuclideanSpace ℝ (Fin 3) → M := N.forward ∘ c.symm
  have hc : ContMDiffOn (𝓡 3) (𝓡 3) ∞ c.symm c.target :=
    contMDiffOn_extChartAt_symm q
  have hchart : Function.Injective
      (mfderiv (𝓡 3) (𝓡 3) c.symm p) := by
    have h := isInvertible_mfderivWithin_extChartAt_symm hp
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using h.injective
  have hinj : Function.Injective
      (mfderiv (𝓡 3) (𝓡 3) e p) := by
    rw [mfderiv_comp p
      ((N.forward_smooth (c.symm p)).mdifferentiableAt (by simp))
      ((hc.contMDiffAt ((isOpen_extChartAt_target q).mem_nhds hp)).mdifferentiableAt
        (by simp))]
    exact (round_forward_mfderiv_injective N (c.symm p)).comp hchart
  let gs : RiemannianMetric 3 M :=
    M13.scaleSmoothMetric g N.scale N.scale_pos
  have hcoeff : roundSourceCoefficients N q = gs.pullbackCoefficients e := by
    funext y
    ext v w
    rfl
  change (roundSourceCoefficients N q p).IsInvertible
  rw [hcoeff]
  exact gs.isInvertible_pullbackCoefficients hinj

theorem round_model_scalar_eq_six
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    (q : N.model.carrier) (p : EuclideanSpace ℝ (Fin 3))
    (hp : p ∈ (extChartAt (𝓡 3) q).target) :
    jetScalarCurvature (roundModelJet N q p) = 6 := by
  let c := extChartAt (𝓡 3) q
  have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ c.symm c.target :=
    contMDiffOn_extChartAt_symm q
  have hi : ∀ y ∈ c.target,
      (mfderiv (𝓡 3) (𝓡 3) c.symm y).IsInvertible := by
    intro y hy
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hy
  have htrace := jetScalarCurvature_metricTwoJet_pullback
    N.model_connection (isOpen_extChartAt_target q) he hi hp
  have hsix := N.model_scalar_eq_six (c.symm p)
  change jetScalarCurvature
      (metricTwoJet (N.model_metric.pullbackCoefficients c.symm) p) = 6
  rw [htrace]
  exact hsix

theorem round_source_scalar_eq
    [T2Space M]
    {g : RiemannianMetric 3 M} {epsilon : ℝ}
    (N : SingularRoundComponent g epsilon)
    (D : LeviCivitaData g)
    (q : N.model.carrier) (p : EuclideanSpace ℝ (Fin 3))
    (hp : p ∈ (extChartAt (𝓡 3) q).target) :
    jetScalarCurvature (roundSourceJet N q p) =
      D.scalarCurvature (N.forward ((extChartAt (𝓡 3) q).symm p)) / N.scale := by
  let c := extChartAt (𝓡 3) q
  let e : EuclideanSpace ℝ (Fin 3) → M := N.forward ∘ c.symm
  have he_chart : ContMDiffOn (𝓡 3) (𝓡 3) ∞ c.symm c.target :=
    contMDiffOn_extChartAt_symm q
  have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e c.target :=
    N.forward_smooth.comp_contMDiffOn he_chart
  have hAall : ∀ y ∈ c.target,
      (mfderiv (𝓡 3) (𝓡 3) e y).IsInvertible := by
    intro y hy
    have hjetInv : (roundSourceJet N q y).1.IsInvertible :=
      round_source_jet_invertible N q y hy
    have hAinj : Function.Injective
        (mfderiv (𝓡 3) (𝓡 3) e y) := by
      apply (injective_iff_map_eq_zero _).mpr
      intro v hv
      apply hjetInv.injective
      rw [map_zero]
      ext w
      change N.scale * g.inner (e y)
        (mfderiv (𝓡 3) (𝓡 3) e y v)
        (mfderiv (𝓡 3) (𝓡 3) e y w) = 0
      rw [hv]
      simp
    let : FiniteDimensional ℝ (TangentSpace (𝓡 3) y) := by
      unfold TangentSpace
      infer_instance
    let : FiniteDimensional ℝ (TangentSpace (𝓡 3) (e y)) := by
      unfold TangentSpace
      infer_instance
    let : T2Space (TangentSpace (𝓡 3) y) :=
      FiberBundle.t2Space (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3)) y
    let : T2Space (TangentSpace (𝓡 3) (e y)) :=
      FiberBundle.t2Space (EuclideanSpace ℝ (Fin 3))
        (TangentSpace (𝓡 3)) (e y)
    have hfin : Module.finrank ℝ (TangentSpace (𝓡 3) y) =
        Module.finrank ℝ (TangentSpace (𝓡 3) (e y)) := by
      unfold TangentSpace
      rfl
    have hAbij : Function.Bijective
        (mfderiv (𝓡 3) (𝓡 3) e y) := by
      refine ⟨hAinj, ?_⟩
      exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp
        hAinj
    exact ⟨(LinearEquiv.ofBijective
        (mfderiv (𝓡 3) (𝓡 3) e y).toLinearMap hAbij).toContinuousLinearEquiv, rfl⟩
  let gs : RiemannianMetric 3 M :=
    M13.scaleSmoothMetric g N.scale N.scale_pos
  let Ds : LeviCivitaData gs :=
    M13.scaleLeviCivitaData D N.scale N.scale_pos
  have htrace := jetScalarCurvature_metricTwoJet_pullback
    Ds (isOpen_extChartAt_target q) he hAall hp
  have hscale := M13.homothety_scalarCurvature_eq g gs
    (Diffeomorph.refl (𝓡 3) M ∞) N.scale N.scale_pos
    (M13.identity_metricHomothety g N.scale N.scale_pos) D Ds (e p)
  change jetScalarCurvature (metricTwoJet (roundSourceCoefficients N q) p) = _
  rw [show roundSourceCoefficients N q = gs.pullbackCoefficients e by
    funext y
    ext v w
    rfl, htrace]
  simpa [gs, Ds, e, c] using hscale

end PoincareConjecture.M28.tube
