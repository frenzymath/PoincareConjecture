import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Convergence.Charts



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology BigOperators InnerProductSpace

noncomputable section

namespace PoincareConjecture.SingularRegularLimit

def sphereFactor (p : RoundCylinderCoordinates) : ℝ :=
  16 / (‖p.1‖ ^ 2 + 4) ^ 2

theorem sphereFactor_pos (p : RoundCylinderCoordinates) : 0 < sphereFactor p := by
  unfold sphereFactor
  positivity

theorem sphereFactor_smooth : ContDiff ℝ ∞ sphereFactor := by
  unfold sphereFactor
  exact contDiff_const.div (((contDiff_fst.norm_sq ℝ).add contDiff_const).pow 2)
    (fun p => by positivity)

theorem cylinderGram_diagonal (u : ℝ) (q : UnitTwoSphere)
    (p : RoundCylinderCoordinates) :
    roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p =
      Matrix.diagonal ![2 * (1 - u) * sphereFactor p,
        2 * (1 - u) * sphereFactor p, 1] := by
  ext a b
  rw [roundCylinderGram_eq_stereographic_formula]
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.diagonal, roundCylinderCoordinateBasis, sphereFactor,
      EuclideanSpace.inner_single_left]

theorem cylinderGram_fderiv (u : ℝ) (q : UnitTwoSphere)
    (p : RoundCylinderCoordinates) (a b : Fin 3) :
    fderiv ℝ (fun r => roundCylinderGram u
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) r a b) p =
      (2 * (1 - u) * ⟪(roundCylinderCoordinateBasis a).1,
        (roundCylinderCoordinateBasis b).1⟫_ℝ) • fderiv ℝ sphereFactor p := by
  have heq : (fun r => roundCylinderGram u
      (chartAt (EuclideanSpace ℝ (Fin 2)) q) r a b) =
      fun r => (2 * (1 - u) * ⟪(roundCylinderCoordinateBasis a).1,
        (roundCylinderCoordinateBasis b).1⟫_ℝ) * sphereFactor r +
        (roundCylinderCoordinateBasis a).2 * (roundCylinderCoordinateBasis b).2 := by
    funext r
    rw [roundCylinderGram_eq_stereographic_formula]
    dsimp only [sphereFactor]
    ring
  rw [heq, fderiv_add_const,
    fderiv_const_mul (sphereFactor_smooth.differentiable (by simp) p)]

theorem sphereFactor_fderiv_axis (p : RoundCylinderCoordinates) :
    fderiv ℝ sphereFactor p (0, 1) = 0 := by
  have heq : sphereFactor = (fun x : EuclideanSpace ℝ (Fin 2) =>
      16 / (‖x‖ ^ 2 + 4) ^ 2) ∘ Prod.fst := rfl
  have hd : DifferentiableAt ℝ
      (fun x : EuclideanSpace ℝ (Fin 2) => 16 / (‖x‖ ^ 2 + 4) ^ 2) p.1 := by
    have h : ContDiff ℝ ∞
        (fun x : EuclideanSpace ℝ (Fin 2) => 16 / (‖x‖ ^ 2 + 4) ^ 2) :=
      contDiff_const.div (((contDiff_id.norm_sq ℝ).add contDiff_const).pow 2)
        (fun x => by positivity)
    exact h.differentiable (by simp) p.1
  rw [heq, fderiv_comp p hd differentiableAt_fst]
  simp [fderiv_fst]

def cylinderWeight (u : ℝ) (p : RoundCylinderCoordinates) (i : Fin 3) : ℝ :=
  ![(2 * (1 - u) * sphereFactor p)⁻¹, (2 * (1 - u) * sphereFactor p)⁻¹, 1] i

theorem cylinderGram_inv_diagonal {u : ℝ} (hu : u ≠ 1) (q : UnitTwoSphere)
    (p : RoundCylinderCoordinates) :
    (roundCylinderGram u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p)⁻¹ =
      Matrix.diagonal (cylinderWeight u p) := by
  have hu' : 1 - u ≠ 0 := sub_ne_zero.mpr hu.symm
  have hp : sphereFactor p ≠ 0 := (sphereFactor_pos p).ne'
  apply Matrix.inv_eq_right_inv
  rw [cylinderGram_diagonal, Matrix.diagonal_mul_diagonal]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.diagonal, cylinderWeight] <;> field_simp

theorem cylinderNorm_diagonal {u : ℝ} (hu : u ≠ 1) (q : UnitTwoSphere)
    (p : RoundCylinderCoordinates) {r : ℕ} (A : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p A =
      ∑ a : Fin r → Fin 3, (∏ i, cylinderWeight u p (a i)) * (A a) ^ 2 := by
  unfold roundCylinderTensorNormSquared
  rw [cylinderGram_inv_diagonal hu]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single a]
  · simp only [Matrix.diagonal_apply_eq]
    ring
  · intro b _ hba
    have hab : a ≠ b := Ne.symm hba
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hab
    have hp : (∏ i, Matrix.diagonal (cylinderWeight u p) (a i) (b i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.diagonal_apply_ne _ hi)
    rw [hp, zero_mul, zero_mul]
  · simp



theorem roundCylinderTensorNormSquared_time_mono {u v : ℝ} (huv : u ≤ v) (hv : v < 1)
    (q : UnitTwoSphere) (p : RoundCylinderCoordinates)
    {r : ℕ} (A : (Fin r → Fin 3) → ℝ) :
    roundCylinderTensorNormSquared u (chartAt (EuclideanSpace ℝ (Fin 2)) q) p A ≤
      roundCylinderTensorNormSquared v (chartAt (EuclideanSpace ℝ (Fin 2)) q) p A := by
  have hu : u < 1 := huv.trans_lt hv
  have hs := sphereFactor_pos p
  have hupos : 0 < 2 * (1 - u) * sphereFactor p := by positivity
  have hvpos : 0 < 2 * (1 - v) * sphereFactor p := by positivity
  have hw (i : Fin 3) : 0 ≤ cylinderWeight u p i := by
    fin_cases i
    · exact (inv_pos.mpr hupos).le
    · exact (inv_pos.mpr hupos).le
    · exact zero_le_one
  have hmono (i : Fin 3) : cylinderWeight u p i ≤ cylinderWeight v p i := by
    have hinv : (2 * (1 - u) * sphereFactor p)⁻¹ ≤
        (2 * (1 - v) * sphereFactor p)⁻¹ :=
      (inv_le_inv₀ hupos hvpos).2 (by nlinarith)
    fin_cases i
    · exact hinv
    · exact hinv
    · exact le_rfl
  rw [cylinderNorm_diagonal hu.ne, cylinderNorm_diagonal hv.ne]
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply Finset.prod_le_prod
  · exact fun i _ => hw (a i)
  · exact fun i _ => hmono (a i)




theorem roundCylinderChristoffel_time_eq {u : ℝ} (hu : u ≠ 1)
    (q : UnitTwoSphere) :
    roundCylinderChristoffel u (chartAt (EuclideanSpace ℝ (Fin 2)) q) =
      roundCylinderChristoffel 0 (chartAt (EuclideanSpace ℝ (Fin 2)) q) := by
  funext p a b d
  have hu' : 1 - u ≠ 0 := sub_ne_zero.mpr hu.symm
  have hp : sphereFactor p ≠ 0 := (sphereFactor_pos p).ne'
  simp only [roundCylinderChristoffel, cylinderGram_fderiv]
  rw [cylinderGram_inv_diagonal hu, cylinderGram_inv_diagonal (by norm_num : (0 : ℝ) ≠ 1)]
  fin_cases a <;> fin_cases b <;> fin_cases d <;>
    simp [Matrix.diagonal, cylinderWeight, roundCylinderCoordinateBasis,
      EuclideanSpace.inner_single_left, sphereFactor_fderiv_axis] <;> field_simp



theorem evolvingRoundCylinderMetric_clock_error
    {q Q : ℝ} (hq : q ≠ 0) (hQ : Q ≠ 0) (t T s : ℝ)
    (z : RoundCylinderSpace) (v w : RoundCylinderTangent z) :
    Q / q * EvolvingRoundCylinderMetric ((T - t) * q + s * q / Q) z v w -
        EvolvingRoundCylinderMetric s z v w =
      2 * (Q / q - 1 - Q * (T - t)) * inner ℝ
        (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) z.1 v.1)
        (mfderiv (𝓡 2) (𝓡 3) (fun x : UnitTwoSphere => x.1) z.1 w.1) +
      (Q / q - 1) * (v.2 * w.2) := by
  unfold EvolvingRoundCylinderMetric
  field_simp
  ring

end PoincareConjecture.SingularRegularLimit
