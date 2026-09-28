import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EndTranslationCalculus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34

theorem exists_endTransition_derivative_bound
    {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)
    {K : Set StandardCapSpace} (hK : IsCompact K) (hKU : K ⊆ endReferenceRegion e) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ r : ℝ, (r = -1 ∨ r = 0 ∨ r = 1) → ∀ x ∈ K,
      norm (E := StandardCapSpace →L[ℝ] StandardCapSpace)
        (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e r) x) ≤ M ∧
      (endAxialTranslation e r x ∈ K →
        norm (E := StandardCapSpace →L[ℝ] StandardCapSpace)
          (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e r) x).inverse ≤ M) := by
  have hb (r : ℝ) (hr : -3 < r) :
      ∃ C : ℝ, ∀ x ∈ K, norm (E := StandardCapSpace →L[ℝ] StandardCapSpace)
        (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e r) x) ≤ C := by
    have hc := (endReferenceTranslation_contMDiffOn e hr).contDiffOn.continuousOn_fderiv_of_isOpen
      (endReferenceRegion_isOpen e) (by decide)
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hc.mono hKU)
    refine ⟨C, ?_⟩
    intro x hx
    simpa only [mfderiv_eq_fderiv] using hC x hx
  obtain ⟨Cn, hCn⟩ := hb (-1) (by norm_num)
  obtain ⟨Cz, hCz⟩ := hb 0 (by norm_num)
  obtain ⟨Cp, hCp⟩ := hb 1 (by norm_num)
  let M := max 1 (max Cn (max Cz Cp))
  have hbound (r : ℝ) (hr : r = -1 ∨ r = 0 ∨ r = 1) (x : StandardCapSpace) (hx : x ∈ K) :
      norm (E := StandardCapSpace →L[ℝ] StandardCapSpace)
        (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e r) x) ≤ M := by
    rcases hr with rfl | rfl | rfl
    · exact (hCn x hx).trans ((le_max_left Cn (max Cz Cp)).trans (le_max_right _ _))
    · exact (hCz x hx).trans ((le_max_left Cz Cp).trans
        ((le_max_right Cn _).trans (le_max_right _ _)))
    · exact (hCp x hx).trans ((le_max_right Cz Cp).trans
        ((le_max_right Cn _).trans (le_max_right _ _)))
  refine ⟨M, le_max_left _ _, ?_⟩
  intro r hr x hx
  refine ⟨hbound r hr x hx, ?_⟩
  intro hshift
  have hrpos : -3 < r := by rcases hr with rfl | rfl | rfl <;> norm_num
  have hrneg : -3 < -r := by rcases hr with rfl | rfl | rfl <;> norm_num
  have hneg : -r = -1 ∨ -r = 0 ∨ -r = 1 := by
    rcases hr with rfl | rfl | rfl <;> norm_num
  rw [endAxialTranslation_inverse_mfderiv e r hrpos hrneg (hKU hx) (hKU hshift)]
  exact hbound (-r) hneg _ hshift

end PoincareConjecture.M34
