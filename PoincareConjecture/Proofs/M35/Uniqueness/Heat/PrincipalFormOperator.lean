import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem norm_dirichletPartial_apply_le (K : Set V) (i : Fin n) (u : dirichletForm K) :
    ‖dirichletPartial K i u‖ ≤ ‖u‖ := by
  have hs : ‖dirichletPartial K i u‖ ^ 2 ≤ ∑ j, ‖dirichletPartial K j u‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖dirichletPartial K j u‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have he := dirichletForm_norm_sq K u
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  linarith only [hs, he, sq_nonneg ‖dirichletInclusion K u‖]

theorem norm_dirichletPartial_le_one (K : Set V) (i : Fin n) :
    ‖dirichletPartial K i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using norm_dirichletPartial_apply_le K i u

def dirichletPartialAdjoint (K : Set V) (i : Fin n) : L2 →L[ℝ] dirichletForm K :=
  ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := dirichletForm K) (F := L2)
    (dirichletPartial K i)

def principalFormOperator (K : Set V) (A : Fin n → Fin n → 𝓢(V, ℝ)) :
    dirichletForm K →L[ℝ] dirichletForm K :=
  ∑ i, ∑ j, (dirichletPartialAdjoint K i).comp
    ((schwartzMultiplier (A i j)).comp (dirichletPartial K j))

theorem principalFormOperator_pairing (K : Set V)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) (u v : dirichletForm K) :
    inner ℝ u (principalFormOperator K A v) = principalEnergy K A u v := by
  simp only [principalFormOperator, dirichletPartialAdjoint, sum_apply, inner_sum,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, ← schwartzMultiplier_selfAdjoint,
    principalEnergy]

theorem schwartzMultiplier_sub (a b : 𝓢(V, ℝ)) :
    schwartzMultiplier (a - b) = schwartzMultiplier a - schwartzMultiplier b := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [schwartzMultiplier_coe (a - b) u, schwartzMultiplier_coe a u,
    schwartzMultiplier_coe b u, Lp.coeFn_sub (schwartzMultiplier a u) (schwartzMultiplier b u)]
    with x hab ha hb hs
  change schwartzMultiplier (a - b) u x = (schwartzMultiplier a u - schwartzMultiplier b u) x
  simp only [hab, hs, Pi.sub_apply, ha, hb, sub_apply, sub_mul]

theorem principalFormOperator_sub (K : Set V)
    (A B : Fin n → Fin n → 𝓢(V, ℝ)) :
    principalFormOperator K (fun i j => A i j - B i j) =
      principalFormOperator K A - principalFormOperator K B := by
  simp only [principalFormOperator, schwartzMultiplier_sub, ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.comp_sub, Finset.sum_sub_distrib]

private theorem principal_summand_norm_le (K : Set V)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) {ε : ℝ} (hε : 0 ≤ ε)
    (hA : ∀ i j x, ‖A i j x‖ ≤ ε) (i j : Fin n) :
    ‖(dirichletPartialAdjoint K i).comp
      ((schwartzMultiplier (A i j)).comp (dirichletPartial K j))‖ ≤ ε := by
  have hM : ‖schwartzMultiplier (A i j)‖ ≤ ε :=
    ContinuousLinearMap.opNorm_le_bound _ hε (fun u => norm_schwartzMultiplier_le _ u (hA i j))
  have hleft : ‖dirichletPartialAdjoint K i‖ ≤ 1 := by
    simpa only [dirichletPartialAdjoint, LinearIsometryEquiv.norm_map]
      using norm_dirichletPartial_le_one K i
  have hright : ‖(schwartzMultiplier (A i j)).comp (dirichletPartial K j)‖ ≤ ε :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hM (norm_dirichletPartial_le_one K j)
        (ContinuousLinearMap.opNorm_nonneg _) hε).trans_eq (mul_one _))
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul hleft hright (ContinuousLinearMap.opNorm_nonneg _) zero_le_one).trans_eq
      (one_mul _))

theorem norm_principalFormOperator_le (K : Set V)
    (A : Fin n → Fin n → 𝓢(V, ℝ)) {ε : ℝ} (hε : 0 ≤ ε)
    (hA : ∀ i j x, ‖A i j x‖ ≤ ε) :
    ‖principalFormOperator K A‖ ≤ (n : ℝ) ^ 2 * ε := by
  calc
    ‖principalFormOperator K A‖ ≤ ∑ i, ∑ j,
        ‖(dirichletPartialAdjoint K i).comp
          ((schwartzMultiplier (A i j)).comp (dirichletPartial K j))‖ := by
      unfold principalFormOperator
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ => norm_sum_le _ _))
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ε :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
        principal_summand_norm_le K A hε hA i j))
    _ = (n : ℝ) ^ 2 * ε := by simp [pow_two, mul_assoc]

theorem norm_principalFormOperator_sub_le (K : Set V)
    (A B : Fin n → Fin n → 𝓢(V, ℝ)) {ε : ℝ} (hε : 0 ≤ ε)
    (hAB : ∀ i j x, ‖A i j x - B i j x‖ ≤ ε) :
    ‖principalFormOperator K A - principalFormOperator K B‖ ≤ (n : ℝ) ^ 2 * ε := by
  rw [← principalFormOperator_sub]
  exact norm_principalFormOperator_le K _ hε hAB

end PoincareConjecture.M35.Uniqueness.Heat
