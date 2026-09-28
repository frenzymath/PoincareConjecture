import PoincareConjecture.Proofs.M76.Dehn.Mathlib.AffineIntersectionRanks
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Projection

set_option autoImplicit false

open Set Module

namespace AffineSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_centered_plane_line_coordinates
    (P Q : AffineSubspace ℝ E) (hdim : finrank ℝ E = 3)
    (hP : finrank ℝ P.direction = 2) (hQ : finrank ℝ Q.direction = 1)
    {p : E} (hpP : p ∈ P) (hpQ : p ∈ Q) (hPQ : P ⊔ Q = ⊤) :
    ∃ F : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E, F 0 = p ∧
      (∀ z, F z ∈ P ↔ z.2 = 0) ∧ ∀ z, F z ∈ Q ↔ z.1 = 0 := by
  classical
  have hrank := P.finrank_inf_add_ambient_of_mem_of_sup_top Q hpP hpQ hPQ
  have hinf : finrank ℝ (P.direction ⊓ Q.direction : Submodule ℝ E) = 0 := by
    rw [direction_inf_of_mem hpP hpQ] at hrank
    omega
  have hsup : P.direction ⊔ Q.direction = ⊤ := by
    rw [← direction_sup_eq_sup_direction hpP hpQ, hPQ, direction_top]
  have hcompl : IsCompl P.direction Q.direction :=
    ⟨disjoint_iff.mpr (Submodule.finrank_eq_zero.mp hinf), codisjoint_iff.mpr hsup⟩
  let eP : (ℝ × ℝ) ≃ₗ[ℝ] P.direction := LinearEquiv.ofFinrankEq _ _ (by
    simp [finrank_prod, hP])
  let eQ : ℝ ≃ₗ[ℝ] Q.direction := LinearEquiv.ofFinrankEq _ _ (by simp [hQ])
  let e := (eP.prodCongr eQ).trans (P.direction.prodEquivOfIsCompl Q.direction hcompl)
  have heP (z : (ℝ × ℝ) × ℝ) : e z ∈ P.direction ↔ z.2 = 0 := by
    have h := (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero
      P.direction Q.direction hcompl (x := e z)).symm
    simpa only [e, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.prodCongr_apply, eQ.map_eq_zero_iff] using h
  have heQ (z : (ℝ × ℝ) × ℝ) : e z ∈ Q.direction ↔ z.1 = 0 := by
    have h := (Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero
      P.direction Q.direction hcompl (x := e z)).symm
    simpa only [e, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
      LinearEquiv.prodCongr_apply, eP.map_eq_zero_iff] using h
  let F := e.toAffineEquiv.toContinuousAffineEquiv.trans
    (ContinuousAffineEquiv.constVAdd ℝ E p)
  have hF (z : (ℝ × ℝ) × ℝ) : F z = e z + p := add_comm _ _
  refine ⟨F, ?_, ?_, ?_⟩
  · rw [hF, map_zero, zero_add]
  · intro z
    rw [hF]
    change e z +ᵥ p ∈ P ↔ z.2 = 0
    rw [P.vadd_mem_iff_mem_direction _ hpP, heP]
  · intro z
    rw [hF]
    change e z +ᵥ p ∈ Q ↔ z.1 = 0
    rw [Q.vadd_mem_iff_mem_direction _ hpQ, heQ]

end AffineSubspace
