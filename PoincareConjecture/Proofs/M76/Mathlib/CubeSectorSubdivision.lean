import PoincareConjecture.Proofs.M76.Mathlib.MaxAffineSubdivision
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension










set_option autoImplicit false

open Set

namespace Geometry

variable {ι : Type*}



def signedCubeCoordinate (j : ι ⊕ ι) : (ι → ℝ) →ₗ[ℝ] ℝ :=
  match j with
  | .inl i => LinearMap.proj i
  | .inr i => -LinearMap.proj i




def cubeSectorForms (j : Option (ι ⊕ ι)) : (ι → ℝ) →ᵃ[ℝ] ℝ :=
  match j with
  | none => AffineMap.const ℝ (ι → ℝ) 1
  | some i => (signedCubeCoordinate i).toAffineMap

variable [Fintype ι]



theorem norm_le_of_cubeSectorForms_le (x : ι → ℝ) {r : ℝ}
    (h : ∀ j, cubeSectorForms j x ≤ r) : ‖x‖ ≤ r := by
  have hr : 1 ≤ r := h none
  apply (pi_norm_le_iff_of_nonneg (by linarith)).mpr
  intro i
  rw [Real.norm_eq_abs]
  have hp : x i ≤ r := h (some (.inl i))
  have hn : -x i ≤ r := h (some (.inr i))
  exact abs_le.mpr ⟨by linarith, hp⟩



theorem signedCubeCoordinate_le_norm (j : ι ⊕ ι) (x : ι → ℝ) :
    signedCubeCoordinate j x ≤ ‖x‖ := by
  cases j with
  | inl i =>
    exact (le_abs_self (x i)).trans
      (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i)
  | inr i =>
    exact (neg_le_abs (x i)).trans
      (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i)

namespace SimplicialComplex





theorem exists_cubeSector_subdivision (K : SimplicialComplex ℝ (ι → ℝ))
    (hK : LocallyFinite (fun s : K.faces => convexHull ℝ (s.val : Set (ι → ℝ)))) :
    ∃ D : SimplicialComplex ℝ (ι → ℝ),
      LocallyFinite (fun s : D.faces => convexHull ℝ (s.val : Set (ι → ℝ))) ∧
      D.IsSubdivision K ∧ ∀ s ∈ D.faces,
        (∀ x ∈ convexHull ℝ (s : Set (ι → ℝ)), ‖x‖ ≤ 1) ∨
        ∃ L : (ι → ℝ) →ₗ[ℝ] ℝ,
          ∀ x ∈ convexHull ℝ (s : Set (ι → ℝ)), 1 ≤ L x ∧ ‖x‖ = L x := by
  classical
  have hN (s : Finset (ι → ℝ)) (hs : s ∈ K.faces) :
      s.card ≤ Module.finrank ℝ (ι → ℝ) + 1 := by
    have h := (K.indep hs).card_le_finrank_succ.trans
      (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    simpa only [Fintype.card_coe] using h
  obtain ⟨D, hD, hDK, _, hmax⟩ :=
    K.exists_locallyFinite_subdivision_max_affine hK hN (@cubeSectorForms ι)
  refine ⟨D, hD, hDK, fun s hs => ?_⟩
  obtain ⟨j, hj⟩ := hmax s hs
  cases j with
  | none =>
    left
    intro x hx
    exact norm_le_of_cubeSectorForms_le x (hj x hx)
  | some i =>
    right
    refine ⟨signedCubeCoordinate i, fun x hx => ?_⟩
    exact ⟨hj x hx none,
      le_antisymm (norm_le_of_cubeSectorForms_le x (hj x hx))
        (signedCubeCoordinate_le_norm i x)⟩

end SimplicialComplex
end Geometry
