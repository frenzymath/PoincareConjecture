import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawSpatialCoefficientJets









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set
open scoped SchwartzMap

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)

theorem exists_rawPrincipal_slab_derivative_bound {J I : Set ℝ} (F : RicciFlow n X J)
    (hI : IsCompact I) (hIJ : I ⊆ J) (η : 𝓢(X, ℝ)) (hη : HasCompactSupport η) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ I, ∀ i j x,
      ‖fderiv ℝ (rawCutoffPrincipalCoefficient (F.metric t) η hη i j) x‖ ≤ B := by
  let A := fun t => rawCutoffPrincipalCoefficient (F.metric t) η hη
  let d : ℝ × X → Fin n → Fin n → X →L[ℝ] ℝ :=
    fun p i j => fderiv ℝ (A p.1 i j) p.2
  have hc : ContinuousOn d (I ×ˢ tsupport η) := by
    apply continuousOn_pi.mpr
    intro i
    apply continuousOn_pi.mpr
    intro j
    exact (raw_family_spatial_fderiv_contDiffOn (f := fun t x => A t i j x)
      (rawCutoffPrincipalCoefficient_joint_contDiffOn F η hη i j)).continuousOn.mono
        (prod_mono hIJ (subset_univ _))
  have hbound : ∃ C : ℝ, ∀ p ∈ I ×ˢ tsupport η, ‖d p‖ ≤ C :=
    (hI.prod hη).exists_bound_of_continuousOn hc
  obtain ⟨C, hC⟩ := hbound
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro t ht i j x
  by_cases hx : x ∈ tsupport η
  · exact (norm_le_pi_norm (d (t, x) i) j).trans
      ((norm_le_pi_norm (d (t, x)) i).trans ((hC (t, x) ⟨ht, hx⟩).trans (le_max_right _ _)))
  · have hzero : fderiv ℝ (A t i j) x = 0 := by
      by_contra h
      exact hx (rawCutoffPrincipalCoefficient_tsupport F η hη t i j
        ((support_fderiv_subset ℝ) h))
    rw [hzero, norm_zero]
    exact le_max_left _ _

end PoincareConjecture.M35.Uniqueness.Heat
