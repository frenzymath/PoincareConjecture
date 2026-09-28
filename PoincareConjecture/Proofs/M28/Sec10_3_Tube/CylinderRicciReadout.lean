import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderScalarReadout











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Manifold IsManifold
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.tube

open PoincareConjecture.SpacetimeBounds PoincareConjecture.Proofs.M28.NeckAnalysis

private abbrev CE := EuclideanSpace ℝ (Fin 3)
private abbrev SE := EuclideanSpace ℝ (Fin 2)
private abbrev CI := (𝓡 2).prod 𝓘(ℝ, ℝ)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M}

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem cylinderNeckCoefficients_ricci_eq [T2Space M]
    (N : EpsilonNeck g) (D : LeviCivitaData g)
    (q : UnitTwoSphere) (s : ℝ) {x : CE}
    (hx : x ∈ cylinderNeckChartDomain N q s) (v w : CE) :
    jetRicci (metricTwoJet (cylinderNeckCoefficients N q s) x) v w =
      D.ricci (cylinderNeckChart N q s x)
        (mfderiv (𝓡 3) (𝓡 3) (cylinderNeckChart N q s) x v)
        (mfderiv (𝓡 3) (𝓡 3) (cylinderNeckChart N q s) x w) := by
  let Q : ℝ := N.scale⁻¹ ^ 2
  have hQ : 0 < Q := pow_pos (inv_pos.mpr N.scale_pos) 2
  let gs : RiemannianMetric 3 M := M13.scaleSmoothMetric g Q hQ
  let Ds : LeviCivitaData gs := M13.scaleLeviCivitaData D Q hQ
  have hcoeff : cylinderNeckCoefficients N q s =
      gs.pullbackCoefficients (cylinderNeckChart N q s) := by
    funext y
    ext a b
    rfl
  rw [hcoeff, jetRicci_metricTwoJet_pullback Ds
    (isOpen_cylinderNeckChartDomain N q s)
    (contMDiffOn_cylinderNeckChart N q s)
    (fun _ hy => cylinderNeckChart_mfderiv_isInvertible N q s hy) hx]
  have hscale := M13.homothety_ricci_eq g gs
    (Diffeomorph.refl (𝓡 3) M ∞) Q hQ
    (M13.identity_metricHomothety g Q hQ) D Ds (cylinderNeckChart N q s x)
    (mfderiv (𝓡 3) (𝓡 3) (cylinderNeckChart N q s) x v)
    (mfderiv (𝓡 3) (𝓡 3) (cylinderNeckChart N q s) x w)
  simpa only [Diffeomorph.coe_refl, mfderiv_id, ContinuousLinearMap.id_apply,
    id_eq] using hscale



theorem cylinderNeckChart_mfderiv_zero_apply
    (N : EpsilonNeck g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (v : CE) :
    mfderiv (𝓡 3) (𝓡 3) (cylinderNeckChart N q s) 0 v =
      mfderiv CI (𝓡 3) N.coordinate_map (q, s)
        (cylinderScalarCoordinateEquiv v) := by
  have hc : (chartAt SE q).symm 0 = q := by
    rw [← sphere_chart_center q]
    exact (chartAt SE q).left_inv (mem_chart_source _ q)
  have hd : mfderiv (𝓡 2) (𝓡 2) (chartAt SE q).symm 0 =
      ContinuousLinearMap.id ℝ SE := by
    have h := mfderivWithin_range_extChartAt_symm (I := 𝓡 2) (x := q)
    have hr : range (𝓡 2) = univ := by ext x; simp
    rw [hr, mfderivWithin_univ] at h
    rw [← sphere_chart_center q]
    convert! h using 1
  rw [cylinderNeckChart_mfderiv_apply N q s
    (zero_mem_cylinderNeckChartDomain N q hs), cylinderScalarCoordinates_zero]
  change mfderiv CI (𝓡 3) N.coordinate_map ((chartAt SE q).symm 0, s)
    (mfderiv (𝓡 2) (𝓡 2) (chartAt SE q).symm 0
      (cylinderScalarCoordinateEquiv v).1, (cylinderScalarCoordinateEquiv v).2) = _
  rw [hc, hd]
  rfl



theorem cylinderNeckCoefficients_ricci_zero [T2Space M]
    (N : EpsilonNeck g) (D : LeviCivitaData g) (q : UnitTwoSphere) {s : ℝ}
    (hs : s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (v w : CE) :
    jetRicci (metricTwoJet (cylinderNeckCoefficients N q s) 0) v w =
      D.ricci (N.coordinate_map (q, s))
        (mfderiv CI (𝓡 3) N.coordinate_map (q, s) (cylinderScalarCoordinateEquiv v))
        (mfderiv CI (𝓡 3) N.coordinate_map (q, s) (cylinderScalarCoordinateEquiv w)) := by
  rw [cylinderNeckCoefficients_ricci_eq N D q s
    (zero_mem_cylinderNeckChartDomain N q hs),
    cylinderNeckChart_mfderiv_zero_apply N q hs v,
    cylinderNeckChart_mfderiv_zero_apply N q hs w, cylinderNeckChart_zero]

end PoincareConjecture.M28.tube
