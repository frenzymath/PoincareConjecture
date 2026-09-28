import PoincareConjecture.Proofs.M76.Mathlib.ContractibleIntrinsicExtension
import Mathlib.Analysis.Convex.StdSimplex












set_option autoImplicit false

open Set

variable (ι : Type*) [Fintype ι]



def stdSimplexCore (η : ℝ) : Set (ι → ℝ) :=
  {q | (∀ i, η ≤ q i) ∧ ∑ i, q i = 1}



theorem isClosed_stdSimplexCore (η : ℝ) : IsClosed (stdSimplexCore ι η) := by
  have he : stdSimplexCore ι η =
      (⋂ i, {q : ι → ℝ | η ≤ q i}) ∩ {q | ∑ i, q i = 1} := by
    ext q
    simp [stdSimplexCore]
  rw [he]
  exact (isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))).inter
    (isClosed_eq (continuous_finsetSum _ (fun i _ => continuous_apply i)) continuous_const)



theorem convex_stdSimplexCore (η : ℝ) : Convex ℝ (stdSimplexCore ι η) := by
  intro q hq r hr a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · change η ≤ a * q i + b * r i
    calc
      η = a * η + b * η := by rw [← add_mul, hab, one_mul]
      _ ≤ a * q i + b * r i := add_le_add
        (mul_le_mul_of_nonneg_left (hq.1 i) ha) (mul_le_mul_of_nonneg_left (hr.1 i) hb)
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hq.2, hr.2, mul_one, hab]



theorem stdSimplexCore_subset_stdSimplex {η : ℝ} (hη : 0 ≤ η) :
    stdSimplexCore ι η ⊆ stdSimplex ℝ ι :=
  fun _ hq => ⟨fun i => hη.trans (hq.1 i), hq.2⟩



theorem isCompact_stdSimplexCore {η : ℝ} (hη : 0 ≤ η) :
    IsCompact (stdSimplexCore ι η) :=
  (isCompact_stdSimplex ℝ ι).of_isClosed_subset (isClosed_stdSimplexCore ι η)
    (stdSimplexCore_subset_stdSimplex ι hη)

variable [Nonempty ι]



theorem nonempty_stdSimplexCore {η : ℝ} (hη : (Fintype.card ι : ℝ) * η < 1) :
    (stdSimplexCore ι η).Nonempty := by
  have hn : 0 < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨fun _ => (Fintype.card ι : ℝ)⁻¹, fun i => ?_, ?_⟩
  · rw [inv_eq_one_div, le_div_iff₀ hn]
    nlinarith [hη]
  · simp

namespace ContinuousMap

variable {Y : Type*} [TopologicalSpace Y] [ContractibleSpace Y]





theorem exists_stdSimplexCore_extension {η : ℝ} (hη : 0 ≤ η)
    (hbound : (Fintype.card ι : ℝ) * η < 1)
    (f : C(intrinsicFrontier ℝ (stdSimplexCore ι η), Y)) :
    ∃ g : C(stdSimplexCore ι η, Y),
      ∀ x : intrinsicFrontier ℝ (stdSimplexCore ι η),
        g ⟨x, intrinsicFrontier_subset (isClosed_stdSimplexCore ι η) x.property⟩ = f x :=
  exists_intrinsicFrontier_extension_of_contractible (isCompact_stdSimplexCore ι hη)
    (convex_stdSimplexCore ι η) (nonempty_stdSimplexCore ι hbound) f

end ContinuousMap
