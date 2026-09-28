import PoincareConjecture.Proofs.M35.Uniqueness.Heat.FiniteHilbertMap
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.DirichletLowerOrder










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] {m : ℕ}

@[simp] theorem finiteHilbertSingle_apply (i j : Fin m) (u : H) :
    finiteHilbertSingle i u j = if j = i then u else 0 := by
  simp [finiteHilbertSingle, ContinuousLinearMap.comp_apply]

theorem norm_finiteHilbertSingle_le (i : Fin m) :
    ‖finiteHilbertSingle (H := H) i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ j : Fin m, ‖finiteHilbertSingle i u j‖ ^ 2) ≤ ‖u‖ ^ 2
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

def finiteHilbertMatrix (A : Fin m → Fin m → V →L[ℝ] H) :
    PiLp 2 (fun _ : Fin m => V) →L[ℝ] PiLp 2 (fun _ : Fin m => H) :=
  ∑ i, ∑ j, (finiteHilbertSingle i).comp
    ((A i j).comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => V) j))

@[simp] theorem finiteHilbertMatrix_apply (A : Fin m → Fin m → V →L[ℝ] H)
    (u : PiLp 2 (fun _ : Fin m => V)) (i : Fin m) :
    finiteHilbertMatrix A u i = ∑ j, A i j (u j) := by
  simp [finiteHilbertMatrix,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply]

theorem norm_finiteHilbertMatrix_le
    (A : Fin m → Fin m → V →L[ℝ] H) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ i j, ‖A i j‖ ≤ C) : ‖finiteHilbertMatrix A‖ ≤ (m : ℝ) ^ 2 * C := by
  have hp (j : Fin m) : ‖PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => V) j‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro u
    change ‖u j‖ ≤ 1 * ‖u‖
    simpa only [one_mul] using PiLp.norm_apply_le u j
  have hij (i j : Fin m) : ‖(finiteHilbertSingle i).comp
      ((A i j).comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => V) j))‖ ≤ C := by
    have hinner : ‖(A i j).comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => V) j)‖ ≤ C :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        ((mul_le_mul (hA i j) (hp j) (norm_nonneg _) hC).trans_eq (mul_one C))
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (norm_finiteHilbertSingle_le i) hinner (norm_nonneg _)
        zero_le_one).trans_eq (one_mul C))
  calc
    _ ≤ ∑ i, ∑ j, ‖(finiteHilbertSingle i).comp
        ((A i j).comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => V) j))‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ _i : Fin m, ∑ _j : Fin m, C :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hij i j
    _ = _ := by simp [pow_two, mul_assoc]

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

def dirichletVectorLowerOrder {K : Set E} (hK : IsClosed K)
    (B : Fin m → Fin m → Fin n → 𝓢(E, ℝ)) (C : Fin m → Fin m → 𝓢(E, ℝ)) :
    PiLp 2 (fun _ : Fin m => dirichletForm K) →L[ℝ]
      PiLp 2 (fun _ : Fin m => dirichletValue K) :=
  finiteHilbertMatrix (fun i j => dirichletLowerOrder hK (B i j) (C i j))

theorem norm_dirichletVectorLowerOrder_le {K : Set E} (hK : IsClosed K)
    (B : Fin m → Fin m → Fin n → 𝓢(E, ℝ)) (C : Fin m → Fin m → 𝓢(E, ℝ))
    {M : ℝ} (hM : 0 ≤ M) (hB : ∀ i j k x, ‖B i j k x‖ ≤ M)
    (hC : ∀ i j x, ‖C i j x‖ ≤ M) :
    ‖dirichletVectorLowerOrder hK B C‖ ≤ (m : ℝ) ^ 2 * (((n : ℝ) + 1) * M) :=
  norm_finiteHilbertMatrix_le _ (by positivity)
    (fun i j => norm_dirichletLowerOrder_le hK (B i j) (C i j) hM (hB i j) (hC i j))

end PoincareConjecture.M35.Uniqueness.Heat
