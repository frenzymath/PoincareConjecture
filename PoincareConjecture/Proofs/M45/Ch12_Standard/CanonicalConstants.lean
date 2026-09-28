import PoincareConjecture.Definitions.M35StandardCapUniqueness

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

namespace StandardCapNeighborhood

variable {atlas : StandardCylinderAtlas} {g₀ : StandardInitialMetric}
  {F : MaximalStandardCapFlow g₀} {t epsilon C C' : ℝ} {x : StandardCapSpace}

theorem scalarSup_pos (N : StandardCapNeighborhood atlas F t epsilon C x) :
    0 < scalarCurvatureSupOn (F.metric t) (F.connection t) N.carrier := by
  have hxcore : x ∈ N.closed_core := interior_subset N.center_in_core
  rw [N.closed_core_eq] at hxcore
  have hbounded : BddAbove (Set.range (fun z : {y // y ∈ N.carrier} =>
      (F.connection t).scalarCurvature z.1)) := by
    refine ⟨C * (F.connection t).scalarCurvature x, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact (N.scalar_ratio x hxcore.1 z.1 z.2).le
  exact (N.scalar_pos x hxcore.1).trans_le
    (le_csSup hbounded ⟨⟨x, hxcore.1⟩, rfl⟩)

def mono_constant (N : StandardCapNeighborhood atlas F t epsilon C x)
    (hCC' : C ≤ C') : StandardCapNeighborhood atlas F t epsilon C' x := by
  have hC' : 0 < C' := N.constant_pos.trans_le hCC'
  have hinv : C'⁻¹ ≤ C⁻¹ := (inv_le_inv₀ hC' N.constant_pos).2 hCC'
  have hsup := N.scalarSup_pos
  refine { N with
    constant_pos := hC'
    scalar_ratio := ?_
    diameter_bound := ?_
    volume_bound := ?_
    core_ball := ?_
    gradient_bound := ?_
    time_derivative_bound := ?_ }
  · intro y hy z hz
    exact (N.scalar_ratio y hy z hz).trans_le
      (mul_le_mul_of_nonneg_right hCC' (N.scalar_pos y hy).le)
  · intro y hy z hz
    exact (N.diameter_bound y hy z hz).trans_le
      (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hCC' (Real.rpow_nonneg hsup.le _)))
  · exact N.volume_bound.trans_le
      (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hCC' (Real.rpow_nonneg hsup.le _)))
  · intro y hy
    obtain ⟨r, hr, hscalar, hsubset, hcompact, hvolume⟩ := N.core_ball y hy
    refine ⟨r, hr, hscalar, hsubset, hcompact, ?_⟩
    exact (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hinv (pow_nonneg hr.le 3))).trans_lt hvolume
  · intro y hy
    exact (N.gradient_bound y hy).trans_le
      (mul_le_mul_of_nonneg_right hCC' (Real.rpow_nonneg (N.scalar_pos y hy).le _))
  · intro y hy
    exact (N.time_derivative_bound y hy).trans_le
      (mul_le_mul_of_nonneg_right hCC' (sq_nonneg _))

end StandardCapNeighborhood

theorem StandardCanonicalAlternative.mono_constant
    {atlas : StandardCylinderAtlas} {g₀ : StandardInitialMetric}
    {F : MaximalStandardCapFlow g₀} {t epsilon C C' : ℝ} {x : StandardCapSpace}
    (h : StandardCanonicalAlternative atlas F t x epsilon C) (hCC' : C ≤ C') :
    StandardCanonicalAlternative atlas F t x epsilon C' := by
  cases h with
  | cap N => exact .cap (N.mono_constant hCC')
  | initial_neck N hdisjoint => exact .initial_neck N hdisjoint
  | evolving_neck N => exact .evolving_neck N

namespace M45

theorem standardCanonicalServices {g₀ : StandardInitialMetric}
    {E : RepairedStandardCapExistenceData g₀}
    (U : RepairedStandardCapUniquenessData g₀ E)
    (gamma lowerConstant : ℝ) (hgamma : 0 < gamma) (hhalf : gamma < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ 1 ≤ C ∧ lowerConstant ≤ C ∧
      ∀ t ∈ Set.Ico 0 E.flow.base.lifetime, ∀ x : StandardCapSpace,
        StandardCanonicalAlternative E.atlas E.flow t x gamma C := by
  obtain ⟨C, hC, hcanonical⟩ := U.canonical gamma hgamma hhalf
  refine ⟨max C (max 1 lowerConstant), hC.trans_le (le_max_left _ _),
    (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _), ?_⟩
  intro t ht x
  exact (hcanonical t ht x).mono_constant (le_max_left _ _)

end M45

end PoincareConjecture
