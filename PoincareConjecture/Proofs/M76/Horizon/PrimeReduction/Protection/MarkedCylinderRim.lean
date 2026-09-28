import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.HomotopyFundamentalGroup
import PoincareConjecture.Proofs.M76.Brown.SpindleHeight
import Mathlib.Topology.OpenPartialHomeomorph.Constructions




noncomputable section

open Set BrownCollar

namespace PoincareConjecture.M76

variable {X Y B : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace B]


def initialRimHomotopyEquiv (X : Type*) [TopologicalSpace X] :
    ContinuousMap.HomotopyEquiv X (X × Icc (0 : ℝ) 1) where
  toFun := ⟨fun x => (x, ⟨0, by norm_num⟩), continuous_id.prodMk continuous_const⟩
  invFun := ContinuousMap.fst
  left_inv := by rfl
  right_inv := by
    refine ⟨{
      toFun := fun z => (z.2.1, ⟨(z.1 : ℝ) * (z.2.2 : ℝ),
        mul_nonneg z.1.property.1 z.2.2.property.1,
        (mul_le_mul_of_nonneg_right z.1.property.2 z.2.2.property.1).trans
          (by simpa using z.2.2.property.2)⟩)
      continuous_toFun := (continuous_fst.comp continuous_snd).prodMk
        (((continuous_subtype_val.comp continuous_fst).mul
          (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))).subtype_mk _)
      map_zero_left := ?_
      map_one_left := ?_ }⟩
    · intro x
      apply Prod.ext
      · rfl
      · exact Subtype.ext (zero_mul _)
    · intro x
      apply Prod.ext
      · rfl
      · exact Subtype.ext (one_mul _)


theorem marked_cylinder_rim_generates (H : (X × Icc (0 : ℝ) 1) ≃ₜ Y)
    (e : X ≃ₜ B) (i : C(B, Y))
    (hmark : ∀ x, H (x, ⟨0, by norm_num⟩) = i (e x)) (b : B) :
    Function.Surjective (FundamentalGroup.map i b) := by
  let E := (e.symm.toHomotopyEquiv.trans (initialRimHomotopyEquiv X)).trans
    H.toHomotopyEquiv
  have hE : E.toFun = i := by
    ext x
    exact (hmark (e.symm x)).trans (congrArg i (e.apply_symm_apply x))
  subst i
  exact (FundamentalGroup.map_bijective_of_homotopyEquiv E b).2



theorem exists_marked_cylinder_rim_collar (H : (X × Icc (0 : ℝ) 1) ≃ₜ Y)
    (e : X ≃ₜ B) (i : B → Y)
    (hmark : ∀ x, H (x, ⟨0, by norm_num⟩) = i (e x)) (b : B) :
    ∃ c : OpenPartialHomeomorph (B × Ico (0 : ℝ) 1) Y,
      c.source = univ ∧ ∀ a, c (collarBase a) = i a := by
  let j : Ico (0 : ℝ) 1 → Icc (0 : ℝ) 1 := inclusion Ico_subset_Icc_self
  have hj : Topology.IsOpenEmbedding j := by
    apply Topology.IsOpenEmbedding.inclusion
    have heq : (Subtype.val : Icc (0 : ℝ) 1 → ℝ) ⁻¹' Ico 0 1 =
        {t : Icc (0 : ℝ) 1 | (t : ℝ) < 1} := by
      ext t
      simp only [mem_preimage, mem_Ico, mem_ofPred_eq, t.property.1, true_and]
    rw [heq]
    exact isOpen_lt continuous_subtype_val continuous_const
  let f : B × Ico (0 : ℝ) 1 → Y := fun z => H (e.symm z.1, j z.2)
  have hf : Topology.IsOpenEmbedding f :=
    H.isOpenEmbedding.comp (e.symm.isOpenEmbedding.prodMap hj)
  let : Nonempty (B × Ico (0 : ℝ) 1) := ⟨collarBase b⟩
  refine ⟨hf.toOpenPartialHomeomorph f, rfl, ?_⟩
  intro a
  change H (e.symm a, ⟨0, _⟩) = i a
  exact (hmark (e.symm a)).trans (congrArg i (e.apply_symm_apply a))

end PoincareConjecture.M76
