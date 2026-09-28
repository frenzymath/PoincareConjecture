import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture

abbrev UnitTwoSphere :=
  {x : EuclideanSpace ℝ (Fin 3) // x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}

abbrev RoundCylinderSpace := UnitTwoSphere × ℝ
abbrev RoundCylinderCoordinates := EuclideanSpace ℝ (Fin 2) × ℝ
abbrev RoundCylinderTangent (z : RoundCylinderSpace) :=
  TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z
abbrev RoundCylinderTwoTensor :=
  (z : RoundCylinderSpace) → RoundCylinderTangent z → RoundCylinderTangent z → ℝ

noncomputable def EvolvingRoundCylinderMetric (u : ℝ) : RoundCylinderTwoTensor :=
  fun z v w ↦
    2 * (1 - u) * inner ℝ
      (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere ↦ x.1) z.1 v.1)
      (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere ↦ x.1) z.1 w.1) +
      v.2 * w.2

noncomputable def RoundCylinderMetric : RoundCylinderTwoTensor :=
  EvolvingRoundCylinderMetric 0

noncomputable def roundCylinderCoordinateBasis : Fin 3 → RoundCylinderCoordinates :=
  ![(EuclideanSpace.basisFun (Fin 2) ℝ 0, 0),
    (EuclideanSpace.basisFun (Fin 2) ℝ 1, 0), (0, 1)]

noncomputable def roundCylinderPullback
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (coordinate : RoundCylinderSpace → M) :
    RoundCylinderTwoTensor :=
  fun z v w ↦ g.inner (coordinate z)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z v)
    (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z w)

noncomputable def roundCylinderTensorCoefficient (B : RoundCylinderTwoTensor)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (p : RoundCylinderCoordinates) (a b : Fin 3) : ℝ :=
  let z : RoundCylinderSpace := (c.symm p.1, p.2)
  let v := roundCylinderCoordinateBasis a
  let w := roundCylinderCoordinateBasis b
  B z (mfderiv (𝓡 2) (𝓡 2) c.symm p.1 v.1, v.2)
    (mfderiv (𝓡 2) (𝓡 2) c.symm p.1 w.1, w.2)

noncomputable def roundCylinderGram (u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (p : RoundCylinderCoordinates) : Matrix (Fin 3) (Fin 3) ℝ :=
  roundCylinderTensorCoefficient (EvolvingRoundCylinderMetric u) c p

noncomputable def roundCylinderChristoffel (u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (p : RoundCylinderCoordinates) (a b d : Fin 3) : ℝ :=
  (1 / 2 : ℝ) * ∑ j : Fin 3, (roundCylinderGram u c p)⁻¹ a j *
    (fderiv ℝ (fun q ↦ roundCylinderGram u c q d j) p
        (roundCylinderCoordinateBasis b) +
      fderiv ℝ (fun q ↦ roundCylinderGram u c q b j) p
        (roundCylinderCoordinateBasis d) -
      fderiv ℝ (fun q ↦ roundCylinderGram u c q b d) p
        (roundCylinderCoordinateBasis j))

noncomputable def roundCylinderTensorDerivative (u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    {r : ℕ} (T : RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ) :
    RoundCylinderCoordinates → (Fin (r + 1) → Fin 3) → ℝ :=
  fun p a ↦
    fderiv ℝ (fun q ↦ T q (fun i ↦ a i.succ)) p
        (roundCylinderCoordinateBasis (a 0)) -
      ∑ i : Fin r, ∑ j : Fin 3,
        roundCylinderChristoffel u c p j (a 0) (a i.succ) *
          T p (Function.update (fun k ↦ a k.succ) i j)

noncomputable def roundCylinderIteratedDerivative (u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (B : RoundCylinderTwoTensor) :
    (k : ℕ) → RoundCylinderCoordinates → (Fin (2 + k) → Fin 3) → ℝ
  | 0 => fun p a ↦ roundCylinderTensorCoefficient B c p (a 0) (a 1) -
      roundCylinderGram u c p (a 0) (a 1)
  | k + 1 => roundCylinderTensorDerivative u c (roundCylinderIteratedDerivative u c B k)

noncomputable def roundCylinderTensorNormSquared (u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    (p : RoundCylinderCoordinates) {r : ℕ} (T : (Fin r → Fin 3) → ℝ) : ℝ :=
  ∑ a : Fin r → Fin 3, ∑ b : Fin r → Fin 3,
    (∏ i : Fin r, (roundCylinderGram u c p)⁻¹ (a i) (b i)) * T a * T b

noncomputable def roundCylinderJetErrorSquared (u : ℝ) (B : RoundCylinderTwoTensor)
    (order : ℕ) (z : RoundCylinderSpace) : ℝ :=
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) z.1
  let p : RoundCylinderCoordinates := (c z.1, z.2)
  ∑ k ∈ Finset.range (order + 1),
    roundCylinderTensorNormSquared u c p (roundCylinderIteratedDerivative u c B k p)

def RoundCylinderTensorSmoothOn (epsilon : ℝ) (B : RoundCylinderTwoTensor) : Prop :=
  ∀ (q : UnitTwoSphere) (a b : Fin 3),
    ContDiffOn ℝ ∞
      (fun p : RoundCylinderCoordinates =>
        roundCylinderTensorCoefficient B
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) p a b)
      ((chartAt (EuclideanSpace ℝ (Fin 2)) q).target ×ˢ
        Set.Ioo (-epsilon⁻¹) epsilon⁻¹)

def RoundCylinderClose (epsilon u : ℝ) (B : RoundCylinderTwoTensor) : Prop :=
  RoundCylinderTensorSmoothOn epsilon B ∧
    ∃ bound : ℝ, bound < epsilon ^ 2 ∧
      ∀ z : RoundCylinderSpace, z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹ →
        roundCylinderJetErrorSquared u B ⌊epsilon⁻¹⌋₊ z ≤ bound

def RoundCylinderFamilyClose (epsilon : ℝ) (I : Set ℝ)
    (B : ℝ → RoundCylinderTwoTensor) : Prop :=
  (∀ u ∈ I, RoundCylinderTensorSmoothOn epsilon (B u)) ∧
    ∃ bound : ℝ, bound < epsilon ^ 2 ∧
      ∀ u ∈ I, ∀ z : RoundCylinderSpace,
        z.2 ∈ Set.Ioo (-epsilon⁻¹) epsilon⁻¹ →
          roundCylinderJetErrorSquared u (B u) ⌊epsilon⁻¹⌋₊ z ≤ bound

end PoincareConjecture
