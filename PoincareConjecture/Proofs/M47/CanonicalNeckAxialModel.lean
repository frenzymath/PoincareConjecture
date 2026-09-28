import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.CylinderJetTranslation
import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.CylinderConnectionParameterBounds
import PoincareConjecture.Proofs.M34.Standard.NeckMetricComparisonCoordinates









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff BigOperators

namespace PoincareConjecture.Proofs.M47

open M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)


def neckAxialWeight (lambda : ℝ) (i : Fin 3) : ℝ :=
  if i = 2 then lambda else 1


def neckAxialCoordinate (lambda c : ℝ) (p : RoundCylinderCoordinates) :
    RoundCylinderCoordinates := (p.1, lambda * p.2 + c)


noncomputable def neckAxialLinearMap (lambda : ℝ) :
    RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates :=
  (ContinuousLinearMap.fst ℝ E₂ ℝ).prod (lambda • ContinuousLinearMap.snd ℝ E₂ ℝ)

theorem neckAxialCoordinate_hasFDerivAt (lambda c : ℝ) (p : RoundCylinderCoordinates) :
    HasFDerivAt (neckAxialCoordinate lambda c) (neckAxialLinearMap lambda) p := by
  exact hasFDerivAt_fst.prodMk ((hasFDerivAt_snd.const_mul lambda).add_const c)

theorem neckAxialLinearMap_basis (lambda : ℝ) (i : Fin 3) :
    neckAxialLinearMap lambda (roundCylinderCoordinateBasis i) =
      neckAxialWeight lambda i • roundCylinderCoordinateBasis i := by
  fin_cases i <;> simp [neckAxialLinearMap, neckAxialWeight, roundCylinderCoordinateBasis]

private theorem gram_axial_derivative_zero (u : ℝ) (q : UnitTwoSphere)
    (p : RoundCylinderCoordinates) (i j : Fin 3) :
    fderiv ℝ (fun y => roundCylinderGram u (chartAt E₂ q) y i j) p
      (roundCylinderCoordinateBasis 2) = 0 := by
  let G := fun y => roundCylinderGram u (chartAt E₂ q) y i j
  have hG : DifferentiableAt ℝ G p :=
    (contDiff_roundCylinderGram u q i j).contDiffAt.differentiableAt (by simp)
  have heq : (fun z : ℝ => G (p.1, z)) = fun _ => G p := by
    funext z
    simp only [G, roundCylinderGram_eq_stereographic_formula]
  have hline : HasFDerivAt (fun z : ℝ => (p.1, z))
      ((0 : ℝ →L[ℝ] E₂).prod (ContinuousLinearMap.id ℝ ℝ)) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have h := hG.hasFDerivAt.comp p.2 hline
  have hh := h.fderiv
  simp only [Function.comp_def] at hh
  rw [heq] at hh
  simp only [fderiv_const_apply] at hh
  have hvalue := congrArg (fun L => L 1) hh
  simpa only [zero_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    roundCylinderCoordinateBasis, Matrix.cons_val, Fin.reduceFinMk] using hvalue.symm


theorem roundCylinderChristoffel_axial_zero (u : ℝ) (q : UnitTwoSphere)
    (p : RoundCylinderCoordinates) (a b d : Fin 3)
    (h : a = 2 ∨ b = 2 ∨ d = 2) :
    roundCylinderChristoffel u (chartAt E₂ q) p a b d = 0 := by
  have hrow (i : Fin 3) : (fun y => roundCylinderGram u (chartAt E₂ q) y 2 i) =
      fun _ => if i = 2 then (1 : ℝ) else 0 := by
    funext y
    rw [roundCylinderGram_chosenChart]
    fin_cases i <;> simp [Matrix.diagonal]
  have hcol (i : Fin 3) : (fun y => roundCylinderGram u (chartAt E₂ q) y i 2) =
      fun _ => if i = 2 then (1 : ℝ) else 0 := by
    funext y
    rw [roundCylinderGram_chosenChart]
    fin_cases i <;> simp [Matrix.diagonal]
  rcases h with rfl | rfl | rfl
  · unfold roundCylinderChristoffel
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j = 2
    · subst j
      rw [hcol, hcol, gram_axial_derivative_zero]
      simp
    · have hinv : (roundCylinderGram u (chartAt E₂ q) p)⁻¹ 2 j = 0 := by
        rw [roundCylinderGram_chosenChart, Matrix.inv_diagonal]
        exact Matrix.diagonal_apply_ne _ (Ne.symm hj)
      rw [hinv, zero_mul]
  · unfold roundCylinderChristoffel
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro j _
    rw [gram_axial_derivative_zero, hrow, hrow]
    simp
  · unfold roundCylinderChristoffel
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro j _
    rw [hrow, hcol, gram_axial_derivative_zero]
    simp



theorem roundCylinderChristoffel_neckAxialCoordinate (lambda c u : ℝ)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates) (a b d : Fin 3) :
    roundCylinderChristoffel u (chartAt E₂ q) (neckAxialCoordinate lambda c p) a b d =
      roundCylinderChristoffel u (chartAt E₂ q) p a b d := by
  have heq : neckAxialCoordinate lambda c p = p + (0, lambda * p.2 + c - p.2) := by
    ext <;> simp [neckAxialCoordinate]
  rw [heq, roundCylinderChristoffel_add_axial]

end PoincareConjecture.Proofs.M47
