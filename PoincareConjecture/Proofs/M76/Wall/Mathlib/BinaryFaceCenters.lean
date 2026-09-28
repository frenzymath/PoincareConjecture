import PoincareConjecture.Proofs.M76.Mathlib.CentroidMesh
import PoincareConjecture.Proofs.M76.Mathlib.DerivedSubdivision










set_option autoImplicit false

open Set
open scoped BigOperators

namespace Finset

variable {E : Type*}




noncomputable def binaryFaceWeights (s : Finset E) (A : Set E) (v : E) : ℝ := by
  classical
  exact if (s.filter (fun x => x ∈ A)).Nonempty ∧
      (s.filter (fun x => x ∉ A)).Nonempty then
    if v ∈ A then (1 / 2 : ℝ) * ((s.filter (fun x => x ∈ A)).card : ℝ)⁻¹
    else (1 / 2 : ℝ) * ((s.filter (fun x => x ∉ A)).card : ℝ)⁻¹
  else (s.card : ℝ)⁻¹



theorem binaryFaceWeights_pos (s : Finset E) (hs : s.Nonempty) (A : Set E) (v : E) :
    0 < s.binaryFaceWeights A v := by
  classical
  by_cases hm : (s.filter (fun x => x ∈ A)).Nonempty ∧
      (s.filter (fun x => x ∉ A)).Nonempty
  · have hp : (0 : ℝ) < (s.filter (fun x => x ∈ A)).card := by
      exact_mod_cast hm.1.card_pos
    have hn : (0 : ℝ) < (s.filter (fun x => x ∉ A)).card := by
      exact_mod_cast hm.2.card_pos
    by_cases hv : v ∈ A
    · simpa only [binaryFaceWeights, if_pos hm, if_pos hv] using
        mul_pos (show (0 : ℝ) < 1 / 2 by norm_num) (inv_pos.mpr hp)
    · simpa only [binaryFaceWeights, if_pos hm, if_neg hv] using
        mul_pos (show (0 : ℝ) < 1 / 2 by norm_num) (inv_pos.mpr hn)
  · simp only [binaryFaceWeights, if_neg hm, inv_pos]
    exact_mod_cast hs.card_pos



theorem sum_binaryFaceWeights (s : Finset E) (hs : s.Nonempty) (A : Set E) :
    (∑ v ∈ s, s.binaryFaceWeights A v) = 1 := by
  classical
  by_cases hm : (s.filter (fun x => x ∈ A)).Nonempty ∧
      (s.filter (fun x => x ∉ A)).Nonempty
  · have hp : ((s.filter (fun x => x ∈ A)).card : ℝ) ≠ 0 := by
      exact_mod_cast hm.1.card_pos.ne'
    have hn : ((s.filter (fun x => x ∉ A)).card : ℝ) ≠ 0 := by
      exact_mod_cast hm.2.card_pos.ne'
    simp only [binaryFaceWeights, if_pos hm, Finset.sum_ite,
      Finset.sum_const, nsmul_eq_mul]
    calc
      _ = (1 / 2 : ℝ) * (((s.filter (fun x => x ∈ A)).card : ℝ) *
            ((s.filter (fun x => x ∈ A)).card : ℝ)⁻¹) +
          (1 / 2 : ℝ) * (((s.filter (fun x => x ∉ A)).card : ℝ) *
            ((s.filter (fun x => x ∉ A)).card : ℝ)⁻¹) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ hp, mul_inv_cancel₀ hn]; norm_num
  · have hs0 : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
    simpa only [binaryFaceWeights, if_neg hm, Finset.sum_const, nsmul_eq_mul] using
      mul_inv_cancel₀ hs0

variable [NormedAddCommGroup E] [NormedSpace ℝ E]



noncomputable def binaryFaceCenter (s : Finset E) (A : Set E) : E :=
  ∑ v ∈ s, s.binaryFaceWeights A v • v



theorem binaryFaceCenter_eq_centroid (s : Finset E) (hs : s.Nonempty) (A : Set E)
    (huniform : (∀ v ∈ s, v ∈ A) ∨ (∀ v ∈ s, v ∉ A)) :
    s.binaryFaceCenter A = s.centroid ℝ id := by
  classical
  have hm : ¬ ((s.filter (fun x => x ∈ A)).Nonempty ∧
      (s.filter (fun x => x ∉ A)).Nonempty) := by
    intro hm
    rcases huniform with h | h
    · obtain ⟨v, hv⟩ := hm.2
      exact (Finset.mem_filter.mp hv).2 (h v (Finset.mem_filter.mp hv).1)
    · obtain ⟨v, hv⟩ := hm.1
      exact h v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2
  rw [s.centroid_eq_inv_card_smul_sum hs]
  simp only [binaryFaceCenter, binaryFaceWeights, if_neg hm, Finset.smul_sum, id_eq]




theorem binaryFaceCenter_of_mixed (s : Finset E) (A : Set E) :
    letI : DecidablePred (fun x : E => x ∈ A) := fun _ => Classical.propDecidable _
    (s.filter (fun x => x ∈ A)).Nonempty ∧
      (s.filter (fun x => x ∉ A)).Nonempty →
    s.binaryFaceCenter A =
      (1 / 2 : ℝ) • (s.filter (fun x => x ∈ A)).centroid ℝ id +
      (1 / 2 : ℝ) • (s.filter (fun x => x ∉ A)).centroid ℝ id := by
  classical
  intro hm
  have hw (v : E) : s.binaryFaceWeights A v =
      if v ∈ A then (1 / 2 : ℝ) * ((s.filter (fun x => x ∈ A)).card : ℝ)⁻¹
      else (1 / 2 : ℝ) * ((s.filter (fun x => x ∉ A)).card : ℝ)⁻¹ := by
    unfold binaryFaceWeights
    split
    · congr
    · rename_i h
      apply (h ?_).elim
      simpa only [Finset.filter_nonempty_iff] using hm
  rw [Finset.centroid_eq_inv_card_smul_sum _ hm.1,
    Finset.centroid_eq_inv_card_smul_sum _ hm.2]
  simp only [binaryFaceCenter, hw, ite_smul,
    Finset.sum_ite, Finset.smul_sum, smul_smul, id_eq]

end Finset

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem positive_binary_face_centers (K : SimplicialComplex ℝ E) (A : Set E)
    (s : K.faces) :
    ∃ w : E → ℝ, (∀ v ∈ s.val, 0 < w v) ∧ (∑ v ∈ s.val, w v) = 1 ∧
      (∑ v ∈ s.val, w v • v) = s.val.binaryFaceCenter A :=
  ⟨s.val.binaryFaceWeights A,
    fun v _ => s.val.binaryFaceWeights_pos (K.nonempty_of_mem_faces s.property) A v,
    s.val.sum_binaryFaceWeights (K.nonempty_of_mem_faces s.property) A, rfl⟩

end Geometry.SimplicialComplex
