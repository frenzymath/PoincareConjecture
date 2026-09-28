import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Transport.Charts
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Acceleration.Parametrization
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.Volume.Coordinates
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Stereographic.Transition










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}


noncomputable def axialCoordinate (N : EpsilonNeck g) : M → ℝ :=
  fun x => (N.coordinate_inverse x).2



noncomputable def finSuccModelEquiv :
    EuclideanSpace ℝ (Fin (2 + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (finCongr (by norm_num))).toContinuousLinearEquiv


noncomputable def axialLinearCoordinate :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).comp
    ((RiemannianMetric.lineModelEquiv 2).symm.toContinuousLinearMap.comp
      (finSuccModelEquiv.symm.toContinuousLinearMap))


noncomputable def euclideanNeckChart (N : EpsilonNeck g) (q : UnitTwoSphere) :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) M := by
  letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let e := roundCylinderModelDiffeomorph
  let c := (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
  exact ((finSuccModelEquiv.symm.toHomeomorph.toOpenPartialHomeomorph.trans
      (RiemannianMetric.productVolumeChart e c)).trans N.coordinatePartialHomeomorph)

@[simp] theorem euclideanNeckChart_apply
    (N : EpsilonNeck g) (q : UnitTwoSphere) (x : EuclideanSpace ℝ (Fin 3)) :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    N.euclideanNeckChart q x =
      N.coordinate_map ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
        ((RiemannianMetric.lineModelEquiv 2).symm
          (finSuccModelEquiv.symm x)).1,
        ((RiemannianMetric.lineModelEquiv 2).symm
          (finSuccModelEquiv.symm x)).2) := by
  letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  rfl

theorem euclideanNeckChart_center_source
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    finSuccModelEquiv (RiemannianMetric.lineModelEquiv 2
      ((0 : EuclideanSpace ℝ (Fin 2)), s)) ∈
      (N.euclideanNeckChart q).source := by
  letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  simp [euclideanNeckChart, OpenPartialHomeomorph.trans_source,
    RiemannianMetric.productVolumeChart_source,
    Poincare.Geometry.Riemannian.SpaceForm.sphere_chart_target,
    cylinderDomain, roundCylinderModelDiffeomorph, hs]
  change ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm 0, s) ∈
    N.coordinatePartialHomeomorph.source
  rw [Poincare.Geometry.Riemannian.SpaceForm.sphere_chart_symm_zero]
  exact ⟨mem_univ _, hs⟩

theorem euclideanNeckChart_center_apply
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    N.euclideanNeckChart q (finSuccModelEquiv (RiemannianMetric.lineModelEquiv 2
      ((0 : EuclideanSpace ℝ (Fin 2)), s))) = N.coordinate_map (q, s) := by
  letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  rw [euclideanNeckChart_apply]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  rw [Poincare.Geometry.Riemannian.SpaceForm.sphere_chart_symm_zero]

theorem euclideanNeckChart_smooth
    (N : EpsilonNeck g) (q : UnitTwoSphere) :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (N.euclideanNeckChart q)
      (N.euclideanNeckChart q).source := by
  letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let e := roundCylinderModelDiffeomorph
  let c := (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
  let a := finSuccModelEquiv.symm.toHomeomorph.toOpenPartialHomeomorph
  have ha : ContMDiffOn (𝓡 3) (𝓡 (2 + 1)) ∞ (a : _ → _) a.source := by
    exact finSuccModelEquiv.symm.contDiff.contMDiff.contMDiffOn
  have hc : ContMDiffOn (𝓡 2) (𝓡 2) ∞ c c.source :=
    contMDiffOn_chart_symm
  have hp := RiemannianMetric.contMDiffOn_productVolumeChart e c hc
  have hn := N.coordinate_map_flat_smooth
  have hap := hp.comp' ha
  simpa [euclideanNeckChart, a, e, c, OpenPartialHomeomorph.trans_source,
    coordinatePartialHomeomorph, cylinderDomain, Function.comp_def] using
    hn.comp' hap

theorem euclideanNeckChart_symm_smooth
    (N : EpsilonNeck g) (q : UnitTwoSphere) :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (N.euclideanNeckChart q).symm
      (N.euclideanNeckChart q).target := by
  letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let e := roundCylinderModelDiffeomorph
  let c := (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
  let a := finSuccModelEquiv.symm.toHomeomorph.toOpenPartialHomeomorph
  have ha : ContMDiffOn (𝓡 (2 + 1)) (𝓡 3) ∞ (a.symm : _ → _) a.target := by
    exact finSuccModelEquiv.contDiff.contMDiff.contMDiffOn
  have hc : ContMDiffOn (𝓡 2) (𝓡 2) ∞ c.symm c.target :=
    contMDiffOn_chart
  have hp := RiemannianMetric.contMDiffOn_productVolumeChart_symm e c hc
  have hn := N.coordinate_inverse_flat_smooth
  have hpn := hp.comp' hn
  simpa [euclideanNeckChart, a, e, c,
    OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_target, coordinatePartialHomeomorph,
    cylinderDomain, Function.comp_def] using ha.comp' hpn

theorem euclideanNeckChart_mdifferentiable
    (N : EpsilonNeck g) (q : UnitTwoSphere) :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    (N.euclideanNeckChart q).MDifferentiable (𝓡 3) (𝓡 3) := by
  letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  exact ⟨(N.euclideanNeckChart_smooth q).mdifferentiableOn (by simp),
    (N.euclideanNeckChart_symm_smooth q).mdifferentiableOn (by simp)⟩

theorem euclideanNeckChart_mfderiv_inverse
    (N : EpsilonNeck g) (q : UnitTwoSphere)
    {p : EuclideanSpace ℝ (Fin 3)}
    (hp : p ∈ (N.euclideanNeckChart q).source)
    (u : TangentSpace (𝓡 3) (N.euclideanNeckChart q p)) :
    mfderiv (𝓡 3) (𝓡 3) (N.euclideanNeckChart q) p
        (mfderiv (𝓡 3) (𝓡 3) (N.euclideanNeckChart q).symm
          (N.euclideanNeckChart q p) u) = u := by
  letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  have hB := N.euclideanNeckChart_mdifferentiable q
  exact (hB.mfderiv hp).right_inv u

theorem euclideanNeckChart_exists_mfderiv_eq
    (N : EpsilonNeck g) (q : UnitTwoSphere)
    {p : EuclideanSpace ℝ (Fin 3)}
    (hp : p ∈ (N.euclideanNeckChart q).source)
    (u : TangentSpace (𝓡 3) (N.euclideanNeckChart q p)) :
    ∃ v : TangentSpace (𝓡 3) p,
      mfderiv (𝓡 3) (𝓡 3) (N.euclideanNeckChart q) p v = u := by
  letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  refine ⟨mfderiv (𝓡 3) (𝓡 3) (N.euclideanNeckChart q).symm
      (N.euclideanNeckChart q p) u, ?_⟩
  exact N.euclideanNeckChart_mfderiv_inverse q hp u

theorem axialCoordinate_comp_euclideanNeckChart
    (N : EpsilonNeck g) (q : UnitTwoSphere)
    {p : EuclideanSpace ℝ (Fin 3)} (hp : p ∈ (N.euclideanNeckChart q).source) :
    axialCoordinate N (N.euclideanNeckChart q p) =
      axialLinearCoordinate ((p : EuclideanSpace ℝ (Fin 3))) := by
  letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  rw [axialCoordinate, euclideanNeckChart_apply]
  have hsource :
      ((finSuccModelEquiv.symm.toHomeomorph.toOpenPartialHomeomorph.trans
        (RiemannianMetric.productVolumeChart roundCylinderModelDiffeomorph
          (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm)) p) ∈
        N.coordinatePartialHomeomorph.source := by
    simpa only [euclideanNeckChart, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_symm, Set.mem_preimage] using hp.2
  have hcoord := N.coordinate_inverse_coordinate_map hsource
  change N.coordinate_inverse
      (N.coordinate_map ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
        ((RiemannianMetric.lineModelEquiv 2).symm
          (finSuccModelEquiv.symm p)).1,
        ((RiemannianMetric.lineModelEquiv 2).symm
          (finSuccModelEquiv.symm p)).2)) =
      ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
        ((RiemannianMetric.lineModelEquiv 2).symm
          (finSuccModelEquiv.symm p)).1,
        ((RiemannianMetric.lineModelEquiv 2).symm
          (finSuccModelEquiv.symm p)).2) at hcoord
  change (N.coordinate_inverse
      (N.coordinate_map ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
        ((RiemannianMetric.lineModelEquiv 2).symm
          (finSuccModelEquiv.symm p)).1,
        ((RiemannianMetric.lineModelEquiv 2).symm
          (finSuccModelEquiv.symm p)).2))).2 = _
  rw [hcoord]
  rfl

theorem axial_hessian_of_euclidean_neckChart
    (N : EpsilonNeck g) (D : LeviCivitaData g) (q : UnitTwoSphere)
    {p : EuclideanSpace ℝ (Fin 3)} (hp : p ∈ (N.euclideanNeckChart q).source)
    (v w : EuclideanSpace ℝ (Fin 3)) :
    letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
    D.hessian (axialCoordinate N) (N.euclideanNeckChart q p)
        (mfderiv (𝓡 3) (𝓡 3) (N.euclideanNeckChart q) p v)
        (mfderiv (𝓡 3) (𝓡 3) (N.euclideanNeckChart q) p w) =
      -axialLinearCoordinate
        (CoordinateExponential.christoffelBilinear
          (g.pullbackCoefficients (N.euclideanNeckChart q)) p v w) := by
  letI := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  apply axial_hessian_of_smooth_parametrization D (N.euclideanNeckChart q)
    (N.euclideanNeckChart_smooth q) (N.euclideanNeckChart_symm_smooth q) hp
  · have hx : N.euclideanNeckChart q p ∈ N.carrier := by
      have hmap := (N.euclideanNeckChart q).map_source hp
      change N.euclideanNeckChart q p ∈
        N.coordinatePartialHomeomorph.target ∩ _ at hmap
      exact hmap.1
    have hi := N.coordinate_inverse_smooth.contMDiffAt
      (N.carrier_open.mem_nhds hx)
    have hsnd : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun z : UnitTwoSphere × ℝ => z.2)
        (N.coordinate_inverse (N.euclideanNeckChart q p)) :=
      contMDiffAt_snd
    exact hsnd.comp _ hi
  · filter_upwards [(N.euclideanNeckChart q).open_source.mem_nhds hp] with x hx
    exact N.axialCoordinate_comp_euclideanNeckChart q hx

end PoincareConjecture.EpsilonNeck
