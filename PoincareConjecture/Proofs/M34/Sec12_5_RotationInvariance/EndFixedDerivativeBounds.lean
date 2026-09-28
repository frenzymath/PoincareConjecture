import PoincareConjecture.Proofs.M34.Sec12_5_RotationInvariance.EndPullbackFlow











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M34




theorem exists_endFixed_derivative_inverse_bound
    {g : RiemannianMetric 3 StandardCapSpace} (e : StandardCylindricalEnd g)
    (s : ℝ) (hs : -3 < s) {K : Set StandardCapSpace} (hK : IsCompact K)
    (hKU : K ⊆ endReferenceRegion e) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ x ∈ K,
      norm (E := StandardCapSpace →L[ℝ] StandardCapSpace)
        (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e s) x) ≤ M ∧
      norm (E := StandardCapSpace →L[ℝ] StandardCapSpace)
        (mfderiv (𝓡 3) (𝓡 3) (endAxialTranslation e s) x).inverse ≤ M := by
  let L : StandardCapSpace → StandardCapSpace →L[ℝ] StandardCapSpace :=
    fun x => fderiv ℝ (endAxialTranslation e s) x
  have hc : ContinuousOn L (endReferenceRegion e) :=
    (endReferenceTranslation_contMDiffOn e hs).contDiffOn.continuousOn_fderiv_of_isOpen
      (endReferenceRegion_isOpen e) (by decide)
  have hi (x : StandardCapSpace) (hx : x ∈ endReferenceRegion e) : (L x).IsInvertible := by
    simpa only [L, mfderiv_eq_fderiv] using endReferenceTranslation_mfderiv_isInvertible e hs hx
  have hci : ContinuousOn (fun x => (L x).inverse) (endReferenceRegion e) := by
    intro x hx
    exact ((hi x hx).contDiffAt_map_inverse (n := 1)).continuousAt.comp_continuousWithinAt (hc x hx)
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (hc.mono hKU)
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn (hci.mono hKU)
  refine ⟨max 1 (max B D), le_max_left _ _, ?_⟩
  intro x hx
  constructor
  · simpa only [L, mfderiv_eq_fderiv] using
      (hB x hx).trans ((le_max_left B D).trans (le_max_right 1 _))
  · simpa only [L, mfderiv_eq_fderiv] using
      (hD x hx).trans ((le_max_right B D).trans (le_max_right 1 _))

end PoincareConjecture.M34
