import PoincareConjecture.Proofs.M35.Uniqueness.RotationAngles

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open scoped Matrix

namespace PoincareConjecture.M35.Uniqueness

theorem standardRotation_basis_apply (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (i j : Fin 3) :
    standardRotation A (EuclideanSpace.single j 1) i = A.1 i j := by
  change (A.1 *ᵥ (EuclideanSpace.single j (1 : ℝ)).ofLp) i = _
  simp [EuclideanSpace.single, Matrix.mulVec, dotProduct]

theorem rotation_axis_stabilizer_entries (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hfix : standardRotation A (EuclideanSpace.single 2 1) = EuclideanSpace.single 2 1) :
    A.1 0 2 = 0 ∧ A.1 1 2 = 0 ∧ A.1 2 2 = 1 ∧ A.1 2 0 = 0 ∧ A.1 2 1 = 0 := by
  have hcol (i : Fin 3) := congrArg (fun x : StandardCapSpace => x i) hfix
  simp only [standardRotation_basis_apply] at hcol
  have h02 : A.1 0 2 = 0 := by simpa [EuclideanSpace.single] using hcol 0
  have h12 : A.1 1 2 = 0 := by simpa [EuclideanSpace.single] using hcol 1
  have h22 : A.1 2 2 = 1 := by simpa [EuclideanSpace.single] using hcol 2
  have horth := (Matrix.mem_specialOrthogonalGroup_iff.mp A.property).1
  have hAA := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp horth
  have hrow := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 2 2) hAA
  norm_num [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three, h22] at hrow
  refine ⟨h02, h12, h22, ?_, ?_⟩
  · nlinarith [sq_nonneg (A.1 2 0), sq_nonneg (A.1 2 1)]
  · nlinarith [sq_nonneg (A.1 2 0), sq_nonneg (A.1 2 1)]

theorem rotation_axis_stabilizer_block (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hfix : standardRotation A (EuclideanSpace.single 2 1) = EuclideanSpace.single 2 1) :
    !![A.1 0 0, A.1 0 1; A.1 1 0, A.1 1 1] ∈
      Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  obtain ⟨h02, h12, h22, h20, h21⟩ := rotation_axis_stabilizer_entries A hfix
  obtain ⟨horth, hdet⟩ := Matrix.mem_specialOrthogonalGroup_iff.mp A.property
  have hAA := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp horth
  rw [Matrix.mem_specialOrthogonalGroup_iff, Matrix.mem_orthogonalGroup_iff]
  constructor
  · ext i j
    have hh (k l : Fin 3) := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M k l) hAA
    fin_cases i <;> fin_cases j
    · simpa [Matrix.mul_apply, Fin.sum_univ_succ, h02, h12] using hh 0 0
    · simpa [Matrix.mul_apply, Fin.sum_univ_succ, h02, h12] using hh 0 1
    · simpa [Matrix.mul_apply, Fin.sum_univ_succ, h02, h12] using hh 1 0
    · simpa [Matrix.mul_apply, Fin.sum_univ_succ, h02, h12] using hh 1 1
  · simpa [Matrix.det_fin_three, h02, h12, h22, h20, h21] using hdet

theorem exists_coordinateRotation_of_fixes_axis
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (hfix : standardRotation A (EuclideanSpace.single 2 1) = EuclideanSpace.single 2 1) :
    ∃ s : ℝ, A = coordinateRotation s := by
  obtain ⟨h02, h12, h22, h20, h21⟩ := rotation_axis_stabilizer_entries A hfix
  obtain ⟨hd, ho, hn⟩ := Matrix.of_mem_specialOrthogonalGroup_fin_two_iff.mp
    (rotation_axis_stabilizer_block A hfix)
  obtain ⟨s, hcos, hsin⟩ := exists_rotation_angle (c := A.1 0 0) (s := A.1 1 0) (by
    rw [ho] at hn
    simpa only [neg_sq] using hn)
  refine ⟨s, Subtype.ext ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateRotation, hcos, hsin, h02, h12, h22, h20, h21, ho, hd]

end PoincareConjecture.M35.Uniqueness
