import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.CovariantSmooth
import PoincareConjecture.Proofs.M28.Prop9_79_Persistence.NeckAnalysis.TensorNorms
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.RoundCylinderChristoffelBound










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.Proofs.M28.NeckAnalysis


theorem roundCylinderChristoffel_center_zero
    (q : UnitTwoSphere) (s : ℝ) (a b d : Fin 3) :
    roundCylinderChristoffel 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q)
      (0, s) a b d = 0 := by
  rw [roundCylinderChristoffel_chosen_chart (by norm_num)]
  have hz (k : Fin 3) : cylinderSphereCoordinate (0, s) k = 0 := by
    fin_cases k <;> rfl
  simp [cylinderModelChristoffel, hz]



theorem roundCylinderTensorDerivative_center
    (q : UnitTwoSphere) (s : ℝ) {r : ℕ}
    (T : RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ)
    (a : Fin r → Fin 3) (i : Fin 3) :
    roundCylinderTensorDerivative 0
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) T (0, s) (Fin.cons i a) =
      fderiv ℝ (fun p => T p a) (0, s) (roundCylinderCoordinateBasis i) := by
  simp [roundCylinderTensorDerivative, roundCylinderChristoffel_center_zero]




theorem second_fderiv_cylinder_component
    (q : UnitTwoSphere) (s : ℝ) {r : ℕ}
    (T : RoundCylinderCoordinates → (Fin r → Fin 3) → ℝ)
    (hT : ∀ a, ContDiffAt ℝ ∞ (fun p => T p a) (0, s))
    (a : Fin r → Fin 3) (i j : Fin 3) :
    fderiv ℝ (fun p => fderiv ℝ (fun y => T y a) p
        (roundCylinderCoordinateBasis i)) (0, s) (roundCylinderCoordinateBasis j) =
      roundCylinderTensorDerivative 0
        (chartAt (EuclideanSpace ℝ (Fin 2)) q)
        (roundCylinderTensorDerivative 0
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) T)
        (0, s) (Fin.cons j (Fin.cons i a)) +
      ∑ b : Fin r, ∑ d : Fin 3,
        fderiv ℝ (fun p => roundCylinderChristoffel 0
          (chartAt (EuclideanSpace ℝ (Fin 2)) q) p d i (a b))
          (0, s) (roundCylinderCoordinateBasis j) * T (0, s) (Function.update a b d) := by
  classical
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let P := fun (b : Fin r) (d : Fin 3) (p : RoundCylinderCoordinates) =>
    roundCylinderChristoffel 0 c p d i (a b) * T p (Function.update a b d)
  have hP (b : Fin r) (d : Fin 3) : DifferentiableAt ℝ (P b d) (0, s) :=
    ((contDiff_roundCylinderChristoffel (by norm_num) q d i (a b)).contDiffAt.mul
      (hT _)).differentiableAt (by simp)
  have hsum : DifferentiableAt ℝ (fun p => ∑ b : Fin r, ∑ d : Fin 3, P b d p)
      (0, s) :=
    DifferentiableAt.fun_sum fun b _ => DifferentiableAt.fun_sum fun d _ => hP b d
  have hlead : DifferentiableAt ℝ
      (fun p => fderiv ℝ (fun y => T y a) p (roundCylinderCoordinateBasis i)) (0, s) :=
    (((hT a).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt
      (by simp)
  have hrec : (fun p => roundCylinderTensorDerivative 0 c T p (Fin.cons i a)) =
      (fun p => fderiv ℝ (fun y => T y a) p (roundCylinderCoordinateBasis i) -
        ∑ b : Fin r, ∑ d : Fin 3, P b d p) := by
    funext p
    simp [roundCylinderTensorDerivative, P]
  have hproduct (b : Fin r) (d : Fin 3) :
      fderiv ℝ (P b d) (0, s) (roundCylinderCoordinateBasis j) =
        fderiv ℝ (fun p => roundCylinderChristoffel 0 c p d i (a b))
          (0, s) (roundCylinderCoordinateBasis j) * T (0, s) (Function.update a b d) := by
    dsimp only [P]
    have hG : DifferentiableAt ℝ
        (fun p => roundCylinderChristoffel 0 c p d i (a b)) (0, s) :=
      ((contDiff_roundCylinderChristoffel (u := 0) (by norm_num)
        q d i (a b)).contDiffAt).differentiableAt (by simp)
    rw [fderiv_fun_mul
      hG ((hT _).differentiableAt (by simp))]
    simp [c, roundCylinderChristoffel_center_zero, mul_comm]
  have hsumder :
      fderiv ℝ (fun p => ∑ b : Fin r, ∑ d : Fin 3, P b d p) (0, s)
          (roundCylinderCoordinateBasis j) =
        ∑ b : Fin r, ∑ d : Fin 3,
          fderiv ℝ (P b d) (0, s) (roundCylinderCoordinateBasis j) := by
    rw [fderiv_fun_sum (fun b _ =>
      DifferentiableAt.fun_sum fun d _ => hP b d)]
    simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro b _
    rw [fderiv_fun_sum (fun d _ => hP b d)]
    simp only [sum_apply]
  rw [roundCylinderTensorDerivative_center, hrec]
  rw [fderiv_fun_sub hlead hsum]
  simp only [sub_apply]
  rw [hsumder]
  simp_rw [hproduct]
  dsimp only [c]
  ring

end PoincareConjecture.Proofs.M28.NeckAnalysis
