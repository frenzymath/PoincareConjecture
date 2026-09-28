import PoincareConjecture.Proofs.M76.Mathlib.HeightPlaneAffineCoordinates
import Mathlib.LinearAlgebra.Dual.Lemmas











set_option autoImplicit false

open Set

namespace AffineSubspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem exists_direction_height_of_codim_one (P : AffineSubspace ℝ E)
    (hdim : Module.finrank ℝ P.direction + 1 = Module.finrank ℝ E)
    {p : E} (hp : p ∈ P) :
    ∃ ell : E →ₗ[ℝ] ℝ, ell ≠ 0 ∧ ∀ x, x ∈ P ↔ ell (x - p) = 0 := by
  have hproper : P.direction ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top] at hdim
    omega
  obtain ⟨ell, hell, hle⟩ :=
    P.direction.exists_le_ker_of_lt_top (lt_top_iff_ne_top.mpr hproper)
  have hker : P.direction = ell.ker := by
    apply Submodule.eq_of_le_of_finrank_eq hle
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero hell
    omega
  refine ⟨ell, hell, ?_⟩
  intro x
  rw [← vsub_right_mem_direction_iff_mem hp x, hker]
  rfl





theorem exists_centered_crossing_coordinates (P Q : AffineSubspace ℝ E)
    (hdim : Module.finrank ℝ E = 3)
    (hP : Module.finrank ℝ P.direction = 2)
    (hQ : Module.finrank ℝ Q.direction = 2) (hjoin : P ⊔ Q = ⊤)
    {p : E} (hpP : p ∈ P) (hpQ : p ∈ Q) :
    ∃ F : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] E,
      F 0 = p ∧ (∀ z, F z ∈ P ↔ z.2 = 0) ∧
      ∀ z, F z ∈ Q ↔ z.1.1 = 0 := by
  have hnot : ¬(P : Set E) ⊆ Q := by
    intro hPQ
    have hPQ' : P ≤ Q := hPQ
    have hQtop : Q = ⊤ := by
      rw [sup_eq_right.mpr hPQ'] at hjoin
      exact hjoin
    rw [hQtop, direction_top, finrank_top] at hQ
    omega
  obtain ⟨u, huP, huQ⟩ := Set.not_subset.mp hnot
  obtain ⟨ell, _, hlevel⟩ := Q.exists_direction_height_of_codim_one (by omega) hpQ
  let A : E →ᵃ[ℝ] ℝ := ell.toAffineMap - AffineMap.const ℝ E (ell p)
  have hAx (x : E) : A x = ell (x - p) := by
    change ell x - ell p = ell (x - p)
    rw [map_sub]
  have hAp : A p = 0 := by rw [hAx, sub_self, map_zero]
  have huA : A u ≠ 0 := by
    intro hu
    exact huQ ((hlevel u).mpr ((hAx u).symm.trans hu))
  have hA : ∃ u ∈ P, ∃ v ∈ P, A u ≠ A v :=
    ⟨u, huP, p, hpP, fun h => huA (h.trans hAp)⟩
  obtain ⟨F, hFzero, hFA, hFP⟩ :=
    P.exists_centered_height_plane_coordinates hdim hP A hA hpP
  refine ⟨F, hFzero, hFP, ?_⟩
  intro z
  calc
    F z ∈ Q ↔ A (F z) = 0 := by rw [hAx]; exact hlevel (F z)
    _ ↔ z.1.1 = 0 := by rw [hFA, hAp, zero_add]

end AffineSubspace
