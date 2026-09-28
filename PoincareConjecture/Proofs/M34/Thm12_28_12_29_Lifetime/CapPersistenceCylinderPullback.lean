import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceEuclideanJets
import PoincareConjecture.Proofs.M34.Standard.NeckMetricComparison
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)


noncomputable def capPersistenceSphereChart (q : UnitTwoSphere) (s : ℝ)
    (x : E₃) : RoundCylinderSpace :=
  cylinderAxialTranslation s (sphereCylinderChart q x)


theorem capPersistenceSphereChart_contMDiff (q : UnitTwoSphere) (s : ℝ) :
    ContMDiff (𝓡 3) Ic ∞ (capPersistenceSphereChart q s) :=
  (cylinderAxialTranslation_contMDiff s).comp (sphereCylinderChart_contMDiff q)



theorem capPersistenceSphereChart_mfderiv (q : UnitTwoSphere) (s : ℝ) (x v : E₃) :
    mfderiv (𝓡 3) Ic (capPersistenceSphereChart q s) x v =
      (mfderiv (𝓡 2) (𝓡 2) (chartAt E₂ q).symm
        (cylinderHorizontal x) (cylinderHorizontal v), v 2) := by
  have h := mfderiv_comp x
    ((cylinderAxialTranslation_contMDiff s _).mdifferentiableAt (by simp))
    ((sphereCylinderChart_contMDiff q x).mdifferentiableAt (by simp))
  have he := congrArg (fun A => A v) h
  change mfderiv (𝓡 3) Ic (capPersistenceSphereChart q s) x v =
    mfderiv Ic Ic (cylinderAxialTranslation s) (sphereCylinderChart q x)
      (mfderiv (𝓡 3) Ic (sphereCylinderChart q) x v) at he
  rw [cylinderAxialTranslation_mfderiv,
    sphereCylinderChart_mfderiv] at he
  exact he


theorem capPersistenceSphereChart_zero (q : UnitTwoSphere) (s : ℝ) :
    capPersistenceSphereChart q s 0 = (q, s) := by
  have hq : (chartAt E₂ q).symm 0 = q := by
    rw [← sphere_chart_center_zero q]
    exact (chartAt E₂ q).left_inv (mem_chart_source E₂ q)
  simp [capPersistenceSphereChart, sphereCylinderChart, cylinderAxialTranslation, hq]



theorem capPersistenceSphereChart_model (q : UnitTwoSphere) (s : ℝ) (x v w : E₃) :
    EvolvingRoundCylinderMetric 0 (capPersistenceSphereChart q s x)
      (mfderiv (𝓡 3) Ic (capPersistenceSphereChart q s) x v)
      (mfderiv (𝓡 3) Ic (capPersistenceSphereChart q s) x w) =
        stereographicCylinderCoefficients 2 x v w := by
  rw [capPersistenceSphereChart_mfderiv, capPersistenceSphereChart_mfderiv]
  have h := standardCylinderInner_sphereCylinderChart q 0 x v w
  rw [sphereCylinderChart_mfderiv, sphereCylinderChart_mfderiv] at h
  simpa only [EvolvingRoundCylinderMetric, standardCylinderInner,
    capPersistenceSphereChart, cylinderAxialTranslation, sphereCylinderChart,
    sub_zero, mul_one] using h

end PoincareConjecture.M34

namespace PoincareConjecture.EpsilonNeck

open M34

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)


noncomputable def capPersistenceEuclideanMap (q : UnitTwoSphere) (s : ℝ) : E₃ → M :=
  N.coordinate_map ∘ capPersistenceSphereChart q s



theorem capPersistenceEuclideanMap_contMDiffAt (q : UnitTwoSphere) (s : ℝ)
    {x : E₃} (hx : x 2 + s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (N.capPersistenceEuclideanMap q s) x := by
  have hz : capPersistenceSphereChart q s x ∈
      univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := ⟨mem_univ _, hx⟩
  exact ((N.coordinate_map_smooth _ hz).contMDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)).comp x
      (capPersistenceSphereChart_contMDiff q s x)



theorem capPersistenceEuclideanMap_mfderiv (q : UnitTwoSphere) (s : ℝ)
    {x : E₃} (hx : x 2 + s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (v : E₃) :
    mfderiv (𝓡 3) (𝓡 3) (N.capPersistenceEuclideanMap q s) x v =
      mfderiv Ic (𝓡 3) N.coordinate_map (capPersistenceSphereChart q s x)
        (mfderiv (𝓡 3) Ic (capPersistenceSphereChart q s) x v) := by
  have hz : capPersistenceSphereChart q s x ∈
      univ ×ˢ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := ⟨mem_univ _, hx⟩
  exact congrArg (fun A => A v) (mfderiv_comp x
    (((N.coordinate_map_smooth _ hz).contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds hz)).mdifferentiableAt (by simp))
    ((capPersistenceSphereChart_contMDiff q s x).mdifferentiableAt (by simp)))



theorem capPersistenceEuclideanMap_coefficient (q : UnitTwoSphere) (s : ℝ)
    {x : E₃} (hx : x 2 + s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (a b : Fin 3) :
    N.scale⁻¹ ^ 2 * g.pullbackCoefficients (N.capPersistenceEuclideanMap q s) x
        (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b) =
      roundCylinderTensorCoefficient
        (fun z v w => N.scale⁻¹ ^ 2 * roundCylinderPullback g N.coordinate_map z v w)
        (chartAt E₂ q) (capPersistenceProductCoordinates x + (0, s)) a b := by
  have hp : capPersistenceProductCoordinates x + (0, s) =
      (cylinderHorizontal x, x 2 + s) := by
    apply Prod.ext
    · change cylinderHorizontal x + 0 = cylinderHorizontal x
      exact add_zero _
    · rfl
  rw [hp]
  change N.scale⁻¹ ^ 2 * g.inner _
    (mfderiv (𝓡 3) (𝓡 3) (N.capPersistenceEuclideanMap q s) x _)
    (mfderiv (𝓡 3) (𝓡 3) (N.capPersistenceEuclideanMap q s) x _) = _
  rw [N.capPersistenceEuclideanMap_mfderiv q s hx,
    N.capPersistenceEuclideanMap_mfderiv q s hx,
    capPersistenceSphereChart_mfderiv, capPersistenceSphereChart_mfderiv]
  have ha := capPersistenceProductCoordinates_basis a
  have hb := capPersistenceProductCoordinates_basis b
  have ha₁ := congrArg Prod.fst ha
  have ha₂ := congrArg Prod.snd ha
  have hb₁ := congrArg Prod.fst hb
  have hb₂ := congrArg Prod.snd hb
  change cylinderHorizontal _ = _ at ha₁ hb₁
  change (EuclideanSpace.basisFun (Fin 3) ℝ a) 2 = _ at ha₂
  change (EuclideanSpace.basisFun (Fin 3) ℝ b) 2 = _ at hb₂
  rw [ha₁, ha₂, hb₁, hb₂]
  rfl

end PoincareConjecture.EpsilonNeck
