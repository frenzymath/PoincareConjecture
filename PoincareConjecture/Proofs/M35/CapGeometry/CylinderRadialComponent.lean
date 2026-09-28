import PoincareConjecture.Proofs.M35.Thm12_28.CurvatureMetricJets
import PoincareConjecture.Proofs.M35.Thm12_28.CylinderCurvature










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "E3" => EuclideanSpace ℝ (Fin 3)

@[instance_reducible] private noncomputable def covectorNormedGroup :
    NormedAddCommGroup (E3 →L[ℝ] ℝ) :=
  inferInstance

attribute [local instance] covectorNormedGroup

@[instance_reducible] private noncomputable def bilinearNormedGroup :
    NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] ℝ) := inferInstance

attribute [local instance] bilinearNormedGroup



theorem cylinder_radial_curvatureTensor_tendsto_zero
    {gseq : ℕ → RiemannianMetric 3 E3} {pseq : ℕ → E3}
    {u s : ℝ} (hu : u < 1) (q : UnitTwoSphere)
    (Dseq : ∀ k, LeviCivitaData (gseq k))
    (hjet : ∀ m ≤ 2, Tendsto
      (fun k => iteratedFDeriv ℝ m (gseq k).euclideanCoefficients (pseq k)) atTop
      (𝓝 (iteratedFDeriv ℝ m (cylinderEuclideanMetric u hu).euclideanCoefficients
        (cylinderCoordinateEquiv.symm ((0, s) : RoundCylinderCoordinates))))) :
    Tendsto (fun k => (Dseq k).curvatureTensor (pseq k)
      (EuclideanSpace.basisFun (Fin 3) ℝ 0)
      (EuclideanSpace.basisFun (Fin 3) ℝ 2)
      (EuclideanSpace.basisFun (Fin 3) ℝ 0)
      (EuclideanSpace.basisFun (Fin 3) ℝ 2)) atTop (𝓝 0) := by
  let D := cylinderEuclideanConnection u hu
  let p := cylinderCoordinateEquiv.symm ((0, s) : RoundCylinderCoordinates)
  have hlim := curvatureTensor_jets_tendsto_of_metric_jets Dseq D pseq p
    (EuclideanSpace.basisFun (Fin 3) ℝ 0)
    (EuclideanSpace.basisFun (Fin 3) ℝ 2)
    (EuclideanSpace.basisFun (Fin 3) ℝ 0)
    (EuclideanSpace.basisFun (Fin 3) ℝ 2) 0 (fun m hm => hjet m (by omega))
  have hlim' : Tendsto (fun k => (Dseq k).curvatureTensor (pseq k)
      (EuclideanSpace.basisFun (Fin 3) ℝ 0)
      (EuclideanSpace.basisFun (Fin 3) ℝ 2)
      (EuclideanSpace.basisFun (Fin 3) ℝ 0)
      (EuclideanSpace.basisFun (Fin 3) ℝ 2)) atTop
      (𝓝 (D.curvatureTensor p
        (EuclideanSpace.basisFun (Fin 3) ℝ 0)
        (EuclideanSpace.basisFun (Fin 3) ℝ 2)
        (EuclideanSpace.basisFun (Fin 3) ℝ 0)
        (EuclideanSpace.basisFun (Fin 3) ℝ 2))) := by
    have h := ((continuousMultilinearCurryFin0 ℝ E3 ℝ).continuous.tendsto _).comp hlim
    simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def,
      LinearIsometryEquiv.apply_symm_apply] using h
  have hzero : D.curvatureTensor p
      (EuclideanSpace.basisFun (Fin 3) ℝ 0)
      (EuclideanSpace.basisFun (Fin 3) ℝ 2)
      (EuclideanSpace.basisFun (Fin 3) ℝ 0)
      (EuclideanSpace.basisFun (Fin 3) ℝ 2) = 0 := by
    rw [cylinder_curvatureTensor_center u hu D q s]
    have hz : (roundCylinderCoordinateBasis 2).1 = 0 := rfl
    rw [hz]
    simp
  rw [hzero] at hlim'
  simpa only [D, p] using hlim'

end PoincareConjecture.M35
