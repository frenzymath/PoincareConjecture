import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalLaplacian
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.PrincipalFormOperator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory
open scoped SchwartzMap LineDeriv

namespace PoincareConjecture.M35.Uniqueness.Heat

open EuclideanDerivativeNative DeTurckGeneratorRegularityNative

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "L2" => Lp ℝ 2 (volume : Measure V)

theorem dirichletPartial_mem_value {K : Set V} (hK : IsClosed K)
    (i : Fin n) (u : dirichletForm K) : dirichletPartial K i u ∈ dirichletValue K := by
  apply (intoDirichletForm_denseRange K).induction_on
    (p := fun u => dirichletPartial K i u ∈ dirichletValue K) u
    ((testValue K).range.isClosed_topologicalClosure.preimage (dirichletPartial K i).continuous)
  intro f
  exact (intoDirichletValue K (testPartial hK i f)).property

def dirichletPartialValue {K : Set V} (hK : IsClosed K) (i : Fin n) :
    dirichletForm K →L[ℝ] dirichletValue K :=
  (dirichletPartial K i).codRestrict (dirichletValue K) (dirichletPartial_mem_value hK i)

theorem dirichletPartialValue_into {K : Set V} (hK : IsClosed K)
    (i : Fin n) (f : supportedTests K) :
    dirichletPartialValue hK i (intoDirichletForm K f) =
      intoDirichletValue K (testPartial hK i f) := rfl

theorem norm_dirichletPartialValue_le_one {K : Set V} (hK : IsClosed K) (i : Fin n) :
    ‖dirichletPartialValue hK i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖dirichletPartial K i u‖ ≤ 1 * ‖u‖
  simpa only [one_mul] using norm_dirichletPartial_apply_le K i u

theorem schwartzMultiplier_mem_value (K : Set V) (a : 𝓢(V, ℝ)) (u : dirichletValue K) :
    schwartzMultiplier a (u : L2) ∈ dirichletValue K := by
  apply (intoDirichletValue_denseRange K).induction_on
    (p := fun u : dirichletValue K => schwartzMultiplier a (u : L2) ∈ dirichletValue K) u
    ((testValue K).range.isClosed_topologicalClosure.preimage
      ((schwartzMultiplier a).continuous.comp continuous_subtype_val))
  intro f
  change schwartzMultiplier a ((f : 𝓢(V, ℝ)).toLp 2 volume) ∈ dirichletValue K
  rw [← testMultiplier_toLp K a f]
  exact (intoDirichletValue K (testMultiplier K a f)).property

def dirichletValueMultiplier (K : Set V) (a : 𝓢(V, ℝ)) :
    dirichletValue K →L[ℝ] dirichletValue K :=
  ((schwartzMultiplier a).comp (dirichletValue K).subtypeL).codRestrict
    (dirichletValue K) (schwartzMultiplier_mem_value K a)

theorem dirichletValueMultiplier_into (K : Set V) (a : 𝓢(V, ℝ)) (f : supportedTests K) :
    dirichletValueMultiplier K a (intoDirichletValue K f) =
      intoDirichletValue K (testMultiplier K a f) := by
  apply Subtype.ext
  exact (testMultiplier_toLp K a f).symm

theorem norm_dirichletValueMultiplier_le (K : Set V) (a : 𝓢(V, ℝ)) {C : ℝ}
    (hC : 0 ≤ C) (ha : ∀ x, ‖a x‖ ≤ C) : ‖dirichletValueMultiplier K a‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro u
  change ‖schwartzMultiplier a (u : L2)‖ ≤ C * ‖(u : L2)‖
  exact norm_schwartzMultiplier_le a (u : L2) ha

def dirichletLowerOrder {K : Set V} (hK : IsClosed K)
    (B : Fin n → 𝓢(V, ℝ)) (C : 𝓢(V, ℝ)) : dirichletForm K →L[ℝ] dirichletValue K :=
  (∑ i, (dirichletValueMultiplier K (B i)).comp (dirichletPartialValue hK i)) +
    (dirichletValueMultiplier K C).comp (dirichletInclusion K)

theorem norm_dirichletLowerOrder_le {K : Set V} (hK : IsClosed K)
    (B : Fin n → 𝓢(V, ℝ)) (C : 𝓢(V, ℝ)) {M : ℝ} (hM : 0 ≤ M)
    (hB : ∀ i x, ‖B i x‖ ≤ M) (hC : ∀ x, ‖C x‖ ≤ M) :
    ‖dirichletLowerOrder hK B C‖ ≤ ((n : ℝ) + 1) * M := by
  have hi (i : Fin n) :
      ‖(dirichletValueMultiplier K (B i)).comp (dirichletPartialValue hK i)‖ ≤ M :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (norm_dirichletValueMultiplier_le K (B i) hM (hB i))
        (norm_dirichletPartialValue_le_one hK i) (norm_nonneg _) hM).trans_eq (mul_one _))
  have hc : ‖(dirichletValueMultiplier K C).comp (dirichletInclusion K)‖ ≤ M :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (norm_dirichletValueMultiplier_le K C hM hC)
        (norm_dirichletInclusion_le_one K) (norm_nonneg _) hM).trans_eq (mul_one _))
  calc
    _ ≤ (∑ i, ‖(dirichletValueMultiplier K (B i)).comp (dirichletPartialValue hK i)‖) + M :=
      (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) hc)
    _ ≤ (∑ _i : Fin n, M) + M := add_le_add (Finset.sum_le_sum (fun i _ => hi i)) le_rfl
    _ = ((n : ℝ) + 1) * M := by simp [add_mul]

end PoincareConjecture.M35.Uniqueness.Heat
