import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Index.Basic














open Set
open scoped NNReal

noncomputable section

namespace Poincare.ODE.Jacobi.IsJacobiSolOn

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem mono {R : ℝ → F →L[ℝ] F} {a b a' b' : ℝ} {y v : ℝ → F}
    (hsol : IsJacobiSolOn R a b y v) (ha : a ≤ a') (hb : b' ≤ b) :
    IsJacobiSolOn R a' b' y v := by
  have hsub : Icc a' b' ⊆ Icc a b := Icc_subset_Icc ha hb
  exact
    { hasDerivWithinAt_fst := fun t ht =>
        (hsol.hasDerivWithinAt_fst t (hsub ht)).mono hsub
      hasDerivWithinAt_snd := fun t ht =>
        (hsol.hasDerivWithinAt_snd t (hsub ht)).mono hsub }


theorem eq_zero_of_interior
    {R : ℝ → F →L[ℝ] F} {a b c C : ℝ} {y v : ℝ → F}
    (hsol : IsJacobiSolOn R a b y v)
    (hc : c ∈ Ioo a b) (hR : ∀ t ∈ Icc a b, ‖R t‖ ≤ C)
    (hyc : y c = 0) (hvc : v c = 0) :
    ∀ t ∈ Icc a b, y t = 0 ∧ v t = 0 := by
  let K : ℝ≥0 := ⟨max 1 C, (zero_le_one.trans (le_max_left _ _))⟩
  have hK : ∀ t ∈ Icc a b, ‖pairCoeff R t‖₊ ≤ K := by
    intro t ht
    exact_mod_cast (norm_pairCoeff_le R t).trans (max_le_max le_rfl (hR t ht))
  have hzero (a' b' : ℝ) :
      Poincare.ODE.Linear.IsSolOn (pairCoeff R) a' b'
        (fun _ => (0 : F × F)) := by
    intro t _
    simpa only [map_zero] using hasDerivWithinAt_const t (Icc a' b') (0 : F × F)
  have hinit : (y c, v c) = (0 : F × F) := by simp [hyc, hvc]
  intro t ht
  have hpair : (y t, v t) = (0 : F × F) := by
    rcases le_total t c with htc | hct
    · exact Poincare.ODE.Linear.IsSolOn.eqOn_of_right
        (fun t ht => hK t ⟨ht.1, ht.2.trans hc.2.le⟩)
        (hsol.mono le_rfl hc.2.le).isSolOn_pair (hzero a c)
        hinit ⟨ht.1, htc⟩
    · exact Poincare.ODE.Linear.IsSolOn.eqOn_of_left
        (fun t ht => hK t ⟨hc.1.le.trans ht.1, ht.2⟩)
        (hsol.mono hc.1.le le_rfl).isSolOn_pair (hzero c b)
        hinit ⟨hct, ht.2⟩
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩


theorem snd_ne_zero
    {R : ℝ → F →L[ℝ] F} {a b c : ℝ} {y v : ℝ → F}
    (hsol : IsJacobiSolOn R a b y v)
    (hc : c ∈ Ioo a b) (hR : ContinuousOn R (Icc a b))
    (hyc : y c = 0) (hne : ∃ t ∈ Icc a b, y t ≠ 0) :
    v c ≠ 0 := by
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hR.norm
  intro hvc
  have hzero := hsol.eq_zero_of_interior hc
    (fun t ht => hC ⟨t, ht, rfl⟩) hyc hvc
  obtain ⟨t, ht, hyt⟩ := hne
  exact hyt (hzero t ht).1

end Poincare.ODE.Jacobi.IsJacobiSolOn
