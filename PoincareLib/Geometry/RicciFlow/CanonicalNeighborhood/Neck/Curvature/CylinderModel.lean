import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geometry.Model
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Bounds.Model
import PoincareLib.Geometry.Riemannian.SpaceForm.SphereCurvature
import PoincareLib.Geometry.Riemannian.SpaceForm.Sectional
import PoincareLib.Geometry.Riemannian.Normalization.Scaling.Curvature
import PoincareLib.Geometry.Riemannian.Metric.Product.Curvature
import PoincareLib.Geometry.Riemannian.Curvature.IntrinsicCalculus
import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.Global.FlowExtension

/-!
# Actual curvature of the scalar-one cylinder

The scalar-one cylinder is the product of the twice-scaled unit two-sphere
with the Euclidean line. Its actual retained connection has scalar curvature
one and Ricci tensor equal to the unit-sphere metric on horizontal vectors.

Reference: Morgan--Tian, Definition 2.18, p. 31; Lemma A.2, pp. 497-498.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology InnerProductSpace
open Poincare.Geometry.Riemannian.SpaceForm

namespace PoincareMT

local instance neckCurvatureCylinderChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) RoundCylinderSpace :=
  RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)

local instance neckCurvatureCylinderIsManifold : IsManifold (𝓡 3) ∞ RoundCylinderSpace :=
  RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)

/-- The actual cylinder metric satisfies the sphere-line product identity. -/
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

/-- The scalar curvature of the actual cylinder metric is one, independently
of the chosen retained Levi-Civita connection. -/
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

/-- The height in the cylinder's product coordinates is parallel and unit. -/
theorem roundCylinderMetric_height (D : LeviCivitaData roundCylinderMetric) :
    RiemannianMetric.HasUnitGradient D (Prod.snd ∘ roundCylinderModelDiffeomorph.symm) ∧
      RiemannianMetric.HasZeroHessian D (Prod.snd ∘ roundCylinderModelDiffeomorph.symm) := by
  let := RiemannianMetric.lineProductChartedSpace (n := 2) (M := UnitTwoSphere)
  let := RiemannianMetric.lineProductIsManifold (n := 2) (M := UnitTwoSphere)
  exact RiemannianMetric.product_height_hasUnitGradient_and_hasZeroHessian
    (rescaledMetric (roundSphereMetric 2) 2 (by norm_num)) roundCylinderMetric D
    roundCylinderModelDiffeomorph roundCylinderMetric_product_inner

/-- Ricci is one half of the metric transverse to the cylinder height. -/
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

/-- Differentiating height in the product coordinates extracts the line component. -/
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

/-- In product tangent coordinates the cylinder Ricci tensor is exactly the
unit-sphere inner product on the two horizontal factors. -/
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

/-- Stereographic sphere coordinates together with the line coordinate,
viewed in the actual three-dimensional cylinder manifold. -/
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

/-- The actual metric pulls back to the fixed cylinder coefficient field. -/
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

/-- The actual Ricci tensor in centered stereographic cylinder coordinates. -/
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

/-- The central product metric has horizontal coefficient two and axial coefficient one. -/
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

/-- At the center of a sphere chart, Ricci is the ordinary horizontal inner product. -/
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

/-- In the frozen horizontal-first coordinate basis, the central Ricci
matrix is exactly `diag(1, 1, 0)`. -/
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

end PoincareMT
