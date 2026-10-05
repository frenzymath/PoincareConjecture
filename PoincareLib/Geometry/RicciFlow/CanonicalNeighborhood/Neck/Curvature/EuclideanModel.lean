import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.MetricJets.Realization
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Curvature.CylinderModel
import PoincareLib.Geometry.Riemannian.Curvature.LocalIsometryInvariants

/-!
# Curvature of the fixed Euclidean cylinder metric

The stereographic parametrization is an actual local isometry for the fixed
Euclidean coefficient metric. Curvature naturality therefore identifies its
scalar curvature and its Ricci tensor, including the horizontal-first central
matrix used in the neck two-jet comparison.

Reference: Morgan--Tian, Lemma A.2, pp. 497-498.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology InnerProductSpace

namespace PoincareMT

local instance neckCurvatureEuclideanCylinderChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) RoundCylinderSpace :=
  RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)

local instance neckCurvatureEuclideanCylinderIsManifold :
    IsManifold (𝓡 3) ∞ RoundCylinderSpace :=
  RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)

/-- The actual cylinder parametrization in the fixed Euclidean model. -/
def roundCylinderEuclideanParametrization (q : UnitTwoSphere)
    (x : EuclideanSpace ℝ (Fin 3)) : RoundCylinderSpace :=
  roundCylinderModelParametrization q ((RiemannianMetric.lineModelEquiv 2).symm x)

theorem contMDiff_roundCylinderEuclideanParametrization (q : UnitTwoSphere) :
    ContMDiff (𝓡 3) (𝓡 3) ∞ (roundCylinderEuclideanParametrization q) :=
  (contMDiff_roundCylinderModelParametrization q).comp
    (RiemannianMetric.lineModelEquiv 2).symm.toContinuousLinearMap.contMDiff

theorem roundCylinderEuclideanParametrization_mfderiv (q : UnitTwoSphere)
    (x v : EuclideanSpace ℝ (Fin 3)) :
    mfderiv (𝓡 3) (𝓡 3) (roundCylinderEuclideanParametrization q) x v =
      mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (roundCylinderModelParametrization q)
        ((RiemannianMetric.lineModelEquiv 2).symm x)
        ((RiemannianMetric.lineModelEquiv 2).symm v) := by
  let T := (RiemannianMetric.lineModelEquiv 2).symm.toContinuousLinearMap
  have h := mfderiv_comp_apply x
    ((contMDiff_roundCylinderModelParametrization q).mdifferentiable (by simp) _)
    T.mdifferentiableAt v
  rw [T.mfderiv_eq] at h
  exact h

/-- The Euclidean coefficient metric is locally isometric to the actual cylinder. -/
theorem roundCylinderEuclideanParametrization_inner (q : UnitTwoSphere)
    (x v w : EuclideanSpace ℝ (Fin 3)) :
    roundCylinderEuclideanMetric.inner x v w =
      roundCylinderMetric.inner (roundCylinderEuclideanParametrization q x)
        (mfderiv (𝓡 3) (𝓡 3) (roundCylinderEuclideanParametrization q) x v)
        (mfderiv (𝓡 3) (𝓡 3) (roundCylinderEuclideanParametrization q) x w) := by
  rw [roundCylinderEuclideanParametrization_mfderiv,
    roundCylinderEuclideanParametrization_mfderiv]
  exact (roundCylinderModelParametrization_inner q
    ((RiemannianMetric.lineModelEquiv 2).symm x)
    ((RiemannianMetric.lineModelEquiv 2).symm v)
    ((RiemannianMetric.lineModelEquiv 2).symm w)).symm

/-- Every retained connection of the fixed Euclidean model has scalar curvature one. -/
theorem roundCylinderEuclideanMetric_scalarCurvature
    (D : LeviCivitaData roundCylinderEuclideanMetric)
    (x : EuclideanSpace ℝ (Fin 3)) : D.scalarCurvature x = 1 := by
  let q : UnitTwoSphere := ⟨EuclideanSpace.basisFun (Fin 3) ℝ 0, by simp⟩
  rw [D.scalarCurvature_eq_of_local_isometry roundCylinderMetric.leviCivitaData isOpen_univ
    (contMDiff_roundCylinderEuclideanParametrization q).contMDiffOn
    (fun y _ v w => roundCylinderEuclideanParametrization_inner q y v w) (mem_univ x),
    roundCylinderMetric_scalarCurvature]

/-- The Ricci tensor of the fixed Euclidean model is the stereographic
unit-sphere metric on its horizontal factors. -/
theorem roundCylinderEuclideanMetric_ricci
    (D : LeviCivitaData roundCylinderEuclideanMetric)
    (x v w : EuclideanSpace ℝ (Fin 3)) :
    D.ricci x v w =
      (16 / (‖((RiemannianMetric.lineModelEquiv 2).symm x).1‖ ^ 2 + 4) ^ 2) *
        ⟪((RiemannianMetric.lineModelEquiv 2).symm v).1,
          ((RiemannianMetric.lineModelEquiv 2).symm w).1⟫_ℝ := by
  let q : UnitTwoSphere := ⟨EuclideanSpace.basisFun (Fin 3) ℝ 0, by simp⟩
  rw [D.ricci_eq_of_local_isometry roundCylinderMetric.leviCivitaData isOpen_univ
    (contMDiff_roundCylinderEuclideanParametrization q).contMDiffOn
    (fun y _ a b => roundCylinderEuclideanParametrization_inner q y a b) (mem_univ x),
    roundCylinderEuclideanParametrization_mfderiv,
    roundCylinderEuclideanParametrization_mfderiv]
  exact roundCylinderModelParametrization_ricci roundCylinderMetric.leviCivitaData q
    ((RiemannianMetric.lineModelEquiv 2).symm x)
    ((RiemannianMetric.lineModelEquiv 2).symm v)
    ((RiemannianMetric.lineModelEquiv 2).symm w)

/-- At zero, Ricci is the ordinary inner product on the horizontal components. -/
theorem roundCylinderEuclideanMetric_ricci_zero
    (D : LeviCivitaData roundCylinderEuclideanMetric)
    (v w : EuclideanSpace ℝ (Fin 3)) :
    D.ricci 0 v w = ⟪((RiemannianMetric.lineModelEquiv 2).symm v).1,
      ((RiemannianMetric.lineModelEquiv 2).symm w).1⟫_ℝ := by
  rw [roundCylinderEuclideanMetric_ricci]
  norm_num

/-- The exact central Ricci matrix in the frozen horizontal-first Euclidean basis. -/
theorem roundCylinderEuclideanMetric_ricci_zero_basis
    (D : LeviCivitaData roundCylinderEuclideanMetric) (i j : Fin 3) :
    D.ricci 0 (roundCylinderEuclideanBasis i) (roundCylinderEuclideanBasis j) =
      if i = j ∧ i ≠ 2 then 1 else 0 := by
  rw [roundCylinderEuclideanMetric_ricci_zero,
    lineModelEquiv_symm_roundCylinderEuclideanBasis,
    lineModelEquiv_symm_roundCylinderEuclideanBasis]
  fin_cases i <;> fin_cases j <;>
    norm_num [roundCylinderCoordinateBasis, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_left, PiLp.single_apply] <;> decide

end PoincareMT
