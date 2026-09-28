import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.EndTranslation
import Mathlib.Analysis.Calculus.FDeriv.Add

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

noncomputable def roundCylinderShift (s : ℝ) (B : RoundCylinderTwoTensor) :
    RoundCylinderTwoTensor := fun z v w => B (cylinderAxialTranslation s z) v w

theorem roundCylinderTensorCoefficient_shift (s : ℝ) (B : RoundCylinderTwoTensor)
    (c : OpenPartialHomeomorph UnitTwoSphere E₂) (p : RoundCylinderCoordinates)
    (a b : Fin 3) :
    roundCylinderTensorCoefficient (roundCylinderShift s B) c p a b =
      roundCylinderTensorCoefficient B c (p + (0, s)) a b := by
  rw [show p + (0, s) = (p.1, p.2 + s) from Prod.ext (add_zero _) rfl]
  rfl

theorem roundCylinderGram_add_axial (s u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere E₂) (p : RoundCylinderCoordinates) :
    roundCylinderGram u c (p + (0, s)) = roundCylinderGram u c p := by
  rw [show p + (0, s) = (p.1, p.2 + s) from Prod.ext (add_zero _) rfl]
  rfl

theorem roundCylinderChristoffel_add_axial (s u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere E₂) (p : RoundCylinderCoordinates)
    (a b d : Fin 3) :
    roundCylinderChristoffel u c (p + (0, s)) a b d =
      roundCylinderChristoffel u c p a b d := by
  have heq (i j : Fin 3) : (fun x => roundCylinderGram u c (x + (0, s)) i j) =
      fun x => roundCylinderGram u c x i j :=
    funext fun x => congrFun (congrFun (roundCylinderGram_add_axial s u c x) i) j
  have hd (i j : Fin 3) :
      fderiv ℝ (fun x => roundCylinderGram u c x i j) (p + (0, s)) =
        fderiv ℝ (fun x => roundCylinderGram u c x i j) p := by
    rw [← fderiv_comp_add_right (0, s), heq]
  simp only [roundCylinderChristoffel, roundCylinderGram_add_axial, hd]

theorem roundCylinderIteratedDerivative_shift (s u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere E₂) (B : RoundCylinderTwoTensor)
    (k : ℕ) (p : RoundCylinderCoordinates) (a : Fin (2 + k) → Fin 3) :
    roundCylinderIteratedDerivative u c (roundCylinderShift s B) k p a =
      roundCylinderIteratedDerivative u c B k (p + (0, s)) a := by
  induction k generalizing p with
  | zero =>
    simp only [roundCylinderIteratedDerivative, roundCylinderTensorCoefficient_shift,
      roundCylinderGram_add_axial]
  | succ k ih =>
    simp only [roundCylinderIteratedDerivative, roundCylinderTensorDerivative]
    simp_rw [ih]
    congr 1
    · convert! congrArg (fun L => L (roundCylinderCoordinateBasis (a 0)))
        (fderiv_comp_add_right (𝕜 := ℝ) (x := p)
          (f := fun y => roundCylinderIteratedDerivative u c B k y (fun i => a i.succ))
          (0, s))
    · simp_rw [roundCylinderChristoffel_add_axial]

theorem roundCylinderTensorNormSquared_add_axial (s u : ℝ)
    (c : OpenPartialHomeomorph UnitTwoSphere E₂) (p : RoundCylinderCoordinates)
    {r : ℕ} (B : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared u c (p + (0, s)) B =
      roundCylinderTensorNormSquared u c p B := by
  simp only [roundCylinderTensorNormSquared, roundCylinderGram_add_axial]

theorem roundCylinderJetErrorSquared_shift (s u : ℝ) (B : RoundCylinderTwoTensor)
    (m : ℕ) (z : RoundCylinderSpace) :
    roundCylinderJetErrorSquared u (roundCylinderShift s B) m z =
      roundCylinderJetErrorSquared u B m (cylinderAxialTranslation s z) := by
  have hp : ((chartAt E₂ z.1) z.1, z.2 + s) =
      ((chartAt E₂ z.1) z.1, z.2) + (0, s) := by simp
  simp only [roundCylinderJetErrorSquared, cylinderAxialTranslation, hp]
  apply Finset.sum_congr rfl
  intro k _
  have hfield : roundCylinderIteratedDerivative u (chartAt E₂ z.1) (roundCylinderShift s B)
      k ((chartAt E₂ z.1) z.1, z.2) =
      roundCylinderIteratedDerivative u (chartAt E₂ z.1) B
        k (((chartAt E₂ z.1) z.1, z.2) + (0, s)) :=
    funext fun a => roundCylinderIteratedDerivative_shift s u _ B k _ a
  rw [hfield, roundCylinderTensorNormSquared_add_axial]

end PoincareConjecture.M34
