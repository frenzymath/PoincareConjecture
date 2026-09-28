import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceCylinderPullback
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.StrongNeckBilinearReadout
import PoincareConjecture.Definitions.Ch11.SingularLimits

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

open M34

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)
local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

theorem capPersistence_tensor_coefficient
    (T : ∀ y : M, TangentSpace (𝓡 3) y → TangentSpace (𝓡 3) y → ℝ)
    (q : UnitTwoSphere) (s : ℝ) {x : E₃}
    (hx : x 2 + s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) (a b : Fin 3) :
    roundCylinderTensorCoefficient (fun z v w => T (N.coordinate_map z)
      (mfderiv Ic (𝓡 3) N.coordinate_map z v)
      (mfderiv Ic (𝓡 3) N.coordinate_map z w)) (chartAt E₂ q)
      (capPersistenceProductCoordinates x + (0, s)) a b =
      T (N.capPersistenceEuclideanMap q s x)
        (mfderiv (𝓡 3) (𝓡 3) (N.capPersistenceEuclideanMap q s) x
          (EuclideanSpace.basisFun (Fin 3) ℝ a))
        (mfderiv (𝓡 3) (𝓡 3) (N.capPersistenceEuclideanMap q s) x
          (EuclideanSpace.basisFun (Fin 3) ℝ b)) := by
  have hp : capPersistenceProductCoordinates x + (0, s) =
      (cylinderHorizontal x, x 2 + s) := by
    apply Prod.ext
    · exact add_zero _
    · rfl
  rw [hp, N.capPersistenceEuclideanMap_mfderiv q s hx,
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

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {J : Set ℝ} {L : BlowupLimitFlow.{u} J}

private local instance : TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance : ChartedSpace E₃ L.carrier.carrier := L.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold

theorem capPersistence_coefficient_difference_fixed_chart
    {G : GeneralizedRicciFlowData.{u}} {origin scale : ℝ} {K : Set ℝ}
    {U : Set L.sliceCarrier.carrier}
    (e : GeneralizedFlowCylinder G L.sliceCarrier origin scale K U)
    (N : EpsilonNeck (L.flow.metric 0)) (q : UnitTwoSphere)
    (s : ℝ) (a : L.sliceCarrier.carrier) (h0 : (0 : ℝ) ∈ K) {x : E₃}
    (hx : x 2 + s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (ha : N.capPersistenceEuclideanMap q s x ∈ (extChartAt (𝓡 3) a).source)
    (i j : Fin 3) :
    let φ := N.capPersistenceEuclideanMap q s
    let f := (extChartAt (𝓡 3) a) ∘ φ
    roundCylinderTensorCoefficient (generalizedCylinderPullback e N.coordinate_map 0)
        (chartAt E₂ q) (capPersistenceProductCoordinates x + (0, s)) i j -
      roundCylinderTensorCoefficient (roundCylinderPullback (L.flow.metric 0) N.coordinate_map)
        (chartAt E₂ q) (capPersistenceProductCoordinates x + (0, s)) i j =
      ((blowupCoordinateBilinear e a 0 (f x) - limitCoordinateBilinear L a 0 (f x)).bilinearComp
        (fderiv ℝ f x) (fderiv ℝ f x))
          (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ j) := by
  dsimp only
  have hφ := (N.capPersistenceEuclideanMap_contMDiffAt q s hx).mdifferentiableAt (by simp)
  have hb := blowupCoordinateBilinear_pullback_apply e a h0 hφ ha
    (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)
  have hl := limitCoordinateBilinear_pullback_apply a 0 hφ ha
    (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)
  have hs := N.capPersistence_tensor_coefficient (e.pullbackInner 0 h0) q s hx i j
  have ht := N.capPersistence_tensor_coefficient
    (fun y v w => (L.flow.metric 0).inner y v w) q s hx i j
  have hread := congrArg₂ (fun v w : ℝ => v - w) hb hl
  simp only [ContinuousLinearMap.bilinearComp_apply, sub_apply] at hread ⊢
  simp only [generalizedCylinderPullback, dif_pos h0]
  exact (congrArg₂ (fun v w : ℝ => v - w) hs ht).trans hread.symm

end PoincareConjecture.M34
