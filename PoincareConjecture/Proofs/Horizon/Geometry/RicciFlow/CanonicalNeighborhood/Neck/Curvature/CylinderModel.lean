import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Model
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Bounds.Model
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.SphereCurvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Sectional
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Product.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.IntrinsicCalculus
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.FlowExtension










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology InnerProductSpace
open Poincare.Geometry.Riemannian.SpaceForm

namespace PoincareConjecture

local instance neckCurvatureCylinderChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) RoundCylinderSpace :=
  RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)

local instance neckCurvatureCylinderIsManifold : IsManifold (𝓡 3) ∞ RoundCylinderSpace :=
  RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)


theorem roundCylinderMetric_product_inner (z : RoundCylinderSpace)
    (v w : RoundCylinderTangent z) :
    roundCylinderMetric.inner (roundCylinderModelDiffeomorph z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) roundCylinderModelDiffeomorph z v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) roundCylinderModelDiffeomorph z w) =
      (rescaledMetric (roundSphereMetric 2) 2 (by norm_num)).inner z.1 v.1 w.1 +
        v.2 * w.2 := by
  rw [roundCylinderMetric_inner, rescaledMetric_inner]
  simp only [EvolvingRoundCylinderMetric, sub_zero, mul_one, roundSphereMetric_inner,
    RiemannianMetric.euclideanMetric_inner]



theorem roundCylinderMetric_scalarCurvature (D : LeviCivitaData roundCylinderMetric)
    (z : RoundCylinderSpace) : D.scalarCurvature z = 1 := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  let gS := roundSphereMetric 2
  let DS := gS.leviCivitaData
  have hS : DS.scalarCurvature z.1 = 2 := by
    have h := DS.scalarCurvature_of_constant_sectional z.1 1
      (roundSphereMetric_sectionalCurvature DS z.1)
    norm_num at h
    exact h
  have hproduct := RiemannianMetric.scalarCurvature_eq_of_line_product
    (rescaledMetric gS 2 (by norm_num)) roundCylinderMetric
    (rescaledMetric_connection gS DS 2 (by norm_num)) D
    roundCylinderModelDiffeomorph roundCylinderMetric_product_inner z
  change D.scalarCurvature z = _ at hproduct
  rw [hproduct, rescaledMetric_scalarCurvature, hS]
  norm_num


theorem roundCylinderMetric_height (D : LeviCivitaData roundCylinderMetric) :
    RiemannianMetric.HasUnitGradient D (Prod.snd ∘ roundCylinderModelDiffeomorph.symm) ∧
      RiemannianMetric.HasZeroHessian D (Prod.snd ∘ roundCylinderModelDiffeomorph.symm) := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  exact RiemannianMetric.product_height_hasUnitGradient_and_hasZeroHessian
    (rescaledMetric (roundSphereMetric 2) 2 (by norm_num)) roundCylinderMetric D
    roundCylinderModelDiffeomorph roundCylinderMetric_product_inner


theorem roundCylinderMetric_ricci_transverse (D : LeviCivitaData roundCylinderMetric)
    (z : RoundCylinderSpace) (v w : TangentSpace (𝓡 3) z) :
    D.ricci z v w = (1 / 2 : ℝ) *
      (roundCylinderMetric.inner z v w -
        mvfderiv (𝓡 3) (Prod.snd ∘ roundCylinderModelDiffeomorph.symm) z v *
          mvfderiv (𝓡 3) (Prod.snd ∘ roundCylinderModelDiffeomorph.symm) z w) := by
  obtain ⟨hu, hz⟩ := roundCylinderMetric_height D
  have hr : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (Prod.snd ∘ roundCylinderModelDiffeomorph.symm) :=
    contMDiff_snd.comp roundCylinderModelDiffeomorph.symm.contMDiff
  simpa only [roundCylinderMetric_scalarCurvature] using
    D.ricci_eq_scalar_transverse_of_parallel_gradient D.intrinsicCurvatureTensorCalculus
      hr hu hz z v w


theorem roundCylinderMetric_height_mvfderiv (z : RoundCylinderSpace)
    (v : RoundCylinderTangent z) :
    mvfderiv (𝓡 3) (Prod.snd ∘ roundCylinderModelDiffeomorph.symm)
      (roundCylinderModelDiffeomorph z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) roundCylinderModelDiffeomorph z v) = v.2 := by
  let e := roundCylinderModelDiffeomorph
  let r : RoundCylinderSpace → ℝ := Prod.snd ∘ e.symm
  have hr : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ r := contMDiff_snd.comp e.symm.contMDiff
  have heq : r ∘ e = Prod.snd := by
    funext x
    simp [r]
  have h := mfderiv_comp_apply z (hr.mdifferentiable (by simp) _)
    (e.contMDiff.mdifferentiable (by simp) _) v
  rw [heq, mfderiv_snd] at h
  exact h.symm



theorem roundCylinderMetric_ricci_product (D : LeviCivitaData roundCylinderMetric)
    (z : RoundCylinderSpace) (v w : RoundCylinderTangent z) :
    D.ricci (roundCylinderModelDiffeomorph z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) roundCylinderModelDiffeomorph z v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) roundCylinderModelDiffeomorph z w) =
      (roundSphereMetric 2).inner z.1 v.1 w.1 := by
  rw [roundCylinderMetric_ricci_transverse, roundCylinderMetric_product_inner,
    roundCylinderMetric_height_mvfderiv, roundCylinderMetric_height_mvfderiv,
    rescaledMetric_inner]
  ring



def roundCylinderModelParametrization (q : UnitTwoSphere)
    (p : RoundCylinderCoordinates) : RoundCylinderSpace :=
  roundCylinderModelDiffeomorph
    ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1, p.2)

theorem contMDiff_roundCylinderModelParametrization (q : UnitTwoSphere) :
    ContMDiff 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) ∞
      (roundCylinderModelParametrization q) := by
  have hc : ContMDiff (𝓡 2) (𝓡 2) ∞
      (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm := by
    rw [← contMDiffOn_univ]
    simpa only [roundCylinder_sphereChart_target] using
      (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞) (x := q))
  let L₁ := ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ
  let L₂ := ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ
  exact roundCylinderModelDiffeomorph.contMDiff.comp
    ((hc.comp L₁.contMDiff).prodMk L₂.contMDiff)

theorem roundCylinderModelParametrization_mfderiv (q : UnitTwoSphere)
    (p v : RoundCylinderCoordinates) :
    mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
      (roundCylinderModelParametrization q) p v =
    mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) roundCylinderModelDiffeomorph
      ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1, p.2)
      (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1 v.1,
        v.2) := by
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  have hc : MDifferentiableAt (𝓡 2) (𝓡 2) c.symm p.1 := by
    apply ((contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞) (x := q)).contMDiffAt
      ?_).mdifferentiableAt (by simp)
    exact c.open_target.mem_nhds (by rw [roundCylinder_sphereChart_target]; trivial)
  let L₁ := ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ
  let L₂ := ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ
  have h₁ := hc.comp p L₁.mdifferentiableAt
  have h₂ := L₂.mdifferentiableAt (x := p)
  have hh := mfderiv_comp p
    (roundCylinderModelDiffeomorph.contMDiff.mdifferentiable (by simp) _) (h₁.prodMk h₂)
  have hL₁ : mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 2) Prod.fst p = L₁ :=
    L₁.mfderiv_eq
  have hL₂ : mfderiv 𝓘(ℝ, RoundCylinderCoordinates) 𝓘(ℝ, ℝ) L₂ p = L₂ :=
    L₂.mfderiv_eq
  rw [mfderiv_prodMk h₁ h₂, mfderiv_comp p hc L₁.mdifferentiableAt, hL₁, hL₂] at hh
  exact congrArg (fun L => L v) hh


theorem roundCylinderModelParametrization_inner (q : UnitTwoSphere)
    (p v w : RoundCylinderCoordinates) :
    roundCylinderMetric.inner (roundCylinderModelParametrization q p)
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
        (roundCylinderModelParametrization q) p v)
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
        (roundCylinderModelParametrization q) p w) = roundCylinderModelCoefficients p v w := by
  rw [roundCylinderModelParametrization_mfderiv, roundCylinderModelParametrization_mfderiv]
  change roundCylinderMetric.inner (roundCylinderModelDiffeomorph _) _ _ = _
  rw [roundCylinderMetric_product_inner, rescaledMetric_inner,
    roundSphereMetric_chart_symm_inner, roundCylinderModelCoefficients_apply]
  ring


theorem roundCylinderModelParametrization_ricci (D : LeviCivitaData roundCylinderMetric)
    (q : UnitTwoSphere) (p v w : RoundCylinderCoordinates) :
    D.ricci (roundCylinderModelParametrization q p)
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
        (roundCylinderModelParametrization q) p v)
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
        (roundCylinderModelParametrization q) p w) =
      (16 / (‖p.1‖ ^ 2 + 4) ^ 2) * ⟪v.1, w.1⟫_ℝ := by
  rw [roundCylinderModelParametrization_mfderiv, roundCylinderModelParametrization_mfderiv]
  change D.ricci (roundCylinderModelDiffeomorph _) _ _ = _
  rw [roundCylinderMetric_ricci_product, roundSphereMetric_chart_symm_inner]


theorem roundCylinderModelParametrization_inner_center (q : UnitTwoSphere)
    (s : ℝ) (v w : RoundCylinderCoordinates) :
    roundCylinderMetric.inner (roundCylinderModelParametrization q (0, s))
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
        (roundCylinderModelParametrization q) (0, s) v)
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
        (roundCylinderModelParametrization q) (0, s) w) =
      2 * ⟪v.1, w.1⟫_ℝ + v.2 * w.2 := by
  rw [roundCylinderModelParametrization_inner, roundCylinderModelCoefficients_apply]
  norm_num


theorem roundCylinderModelParametrization_ricci_center
    (D : LeviCivitaData roundCylinderMetric) (q : UnitTwoSphere)
    (s : ℝ) (v w : RoundCylinderCoordinates) :
    D.ricci (roundCylinderModelParametrization q (0, s))
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
        (roundCylinderModelParametrization q) (0, s) v)
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
        (roundCylinderModelParametrization q) (0, s) w) = ⟪v.1, w.1⟫_ℝ := by
  rw [roundCylinderModelParametrization_ricci]
  norm_num



theorem roundCylinderModelParametrization_ricci_center_basis
    (D : LeviCivitaData roundCylinderMetric) (q : UnitTwoSphere) (s : ℝ) (i j : Fin 3) :
    D.ricci (roundCylinderModelParametrization q (0, s))
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
        (roundCylinderModelParametrization q) (0, s) (roundCylinderCoordinateBasis i))
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3)
        (roundCylinderModelParametrization q) (0, s) (roundCylinderCoordinateBasis j)) =
      if i = j ∧ i ≠ 2 then 1 else 0 := by
  rw [roundCylinderModelParametrization_ricci_center]
  fin_cases i <;> fin_cases j <;>
    norm_num [roundCylinderCoordinateBasis, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_left, PiLp.single_apply] <;> decide

end PoincareConjecture
