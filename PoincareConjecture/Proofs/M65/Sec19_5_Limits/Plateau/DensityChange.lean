import PoincareConjecture.Definitions.Ch18.LoopSpaceWidth
import PoincareConjecture.Proofs.M58.Mathlib.TwoVectorArea
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

open Proofs.M58

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]





theorem m65ParametrizedAreaDensity_comp (g : RiemannianMetric 3 M)
    (f : LoopPlane → M) (φ : LoopPlane → LoopPlane) (z : LoopPlane)
    (hf : MDifferentiableAt (𝓡 2) (𝓡 3) f (φ z))
    (hφ : DifferentiableAt ℝ φ z) :
    parametrizedAreaDensity g (f ∘ φ) z =
      |(fderiv ℝ φ z).det| * parametrizedAreaDensity g f (φ z) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let B := EuclideanSpace.basisFun (Fin 2) ℝ
  let D : LoopPlane →L[ℝ] TangentSpace (𝓡 3) (f (φ z)) :=
    mfderiv (𝓡 2) (𝓡 3) f (φ z)
  let A := fderiv ℝ φ z
  have harea (F : LoopPlane → M) (w : LoopPlane) :
      parametrizedAreaDensity g F w =
        twoVectorArea (mfderiv (𝓡 2) (𝓡 3) F w (B 0))
          (mfderiv (𝓡 2) (𝓡 3) F w (B 1)) := by
    unfold parametrizedAreaDensity twoVectorArea
    dsimp only
    erw [Matrix.det_fin_two]
    let u := mfderiv (𝓡 2) (𝓡 3) F w (B 0)
    let v := mfderiv (𝓡 2) (𝓡 3) F w (B 1)
    change Real.sqrt (max 0 (inner ℝ u u * inner ℝ v v - inner ℝ u v * inner ℝ v u)) = _
    rw [real_inner_comm (mfderiv (𝓡 2) (𝓡 3) F w (B 1))
      (mfderiv (𝓡 2) (𝓡 3) F w (B 0)), pow_two]
  have hrep (w : LoopPlane) : D w = w 0 • D (B 0) + w 1 • D (B 1) := by
    have hw : w = w 0 • B 0 + w 1 • B 1 := by
      simpa only [Fin.sum_univ_two, EuclideanSpace.basisFun_repr] using
        ((EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr w).symm
    calc
      D w = D (w 0 • B 0 + w 1 • B 1) := congrArg D hw
      _ = _ := by erw [map_add, map_smul, map_smul]
  have hdet : A.det = (A (B 0)) 0 * (A (B 1)) 1 - (A (B 0)) 1 * (A (B 1)) 0 := by
    change LinearMap.det A.toLinearMap = _
    rw [← LinearMap.det_toMatrix B.toBasis, Matrix.det_fin_two]
    simp only [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.coe_toBasis, B, EuclideanSpace.basisFun_repr]
    change (A (B 0)) 0 * (A (B 1)) 1 - (A (B 1)) 0 * (A (B 0)) 1 = _
    ring
  rw [harea, harea]
  simp only [mfderiv_comp z hf hφ.mdifferentiableAt, mfderiv_eq_fderiv]
  change twoVectorArea (D (A (B 0))) (D (A (B 1))) =
    |A.det| * twoVectorArea (D (B 0)) (D (B 1))
  rw [hrep (A (B 0)), hrep (A (B 1)), twoVectorArea_change, hdet]

end PoincareConjecture
