import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneDiskProduct
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneStandardProduct
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneMiddleBall










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (ℝ × ℝ)
local notation "W" => (ℝ × V2)

private theorem closure_open_square_annulus :
    closure {v : V2 | (3 / 2 : ℝ) < ‖v‖ ∧ ‖v‖ < 2} =
      {v : V2 | (3 / 2 : ℝ) ≤ ‖v‖ ∧ ‖v‖ ≤ 2} := by
  apply Subset.antisymm
  · exact closure_minimal (fun _ h => ⟨h.1.le, h.2.le⟩)
      ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const))
  · intro v hv
    have hn : 0 < ‖v‖ := by linarith [hv.1]
    let f : ℝ → V2 := fun t => (t / ‖v‖) • v
    have hf : Continuous f := (continuous_id.div_const _).smul continuous_const
    have hmaps : MapsTo f (Ioo (3 / 2 : ℝ) 2)
        {v : V2 | (3 / 2 : ℝ) < ‖v‖ ∧ ‖v‖ < 2} := by
      intro t ht
      have hnorm : ‖f t‖ = t := by
        change ‖(t / ‖v‖) • v‖ = t
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg (by linarith [ht.1]) hn.le), div_mul_cancel₀ _ hn.ne']
      change (3 / 2 : ℝ) < ‖f t‖ ∧ ‖f t‖ < 2
      rwa [hnorm]
    have hcl : ‖v‖ ∈ closure (Ioo (3 / 2 : ℝ) 2) := by
      rw [closure_Ioo (by norm_num : (3 / 2 : ℝ) ≠ 2)]
      exact hv
    have h := hf.continuousWithinAt.mem_closure hcl hmaps
    simpa only [f, div_self hn.ne', one_smul] using h




theorem complementaryRegion_squareMiddleBlock :
    complementaryRegion squareMiddleBlock = squareShell := by
  have hdiff : interior squareBlock \ squareMiddleBlock =
      Ioo (-1 : ℝ) 1 ×ˢ {v : V2 | (3 / 2 : ℝ) < ‖v‖ ∧ ‖v‖ < 2} := by
    rw [squareBlock, interior_prod_eq, interior_Icc,
      interior_closedBall _ (by norm_num)]
    ext x
    simp only [squareMiddleBlock, mem_sdiff, mem_prod, mem_Ioo,
      mem_Icc, mem_ball_zero_iff, mem_closedBall_zero_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hs, hn⟩, hnot⟩
      exact ⟨hs, lt_of_not_ge (fun h => hnot ⟨⟨hs.1.le, hs.2.le⟩, h⟩), hn⟩
    · rintro ⟨hs, hlo, hhi⟩
      exact ⟨⟨hs, hhi⟩, fun h => (not_lt_of_ge h.2) hlo⟩
  rw [complementaryRegion, hdiff, closure_prod_eq,
    closure_Ioo (by norm_num : (-1 : ℝ) ≠ 1), closure_open_square_annulus]
  rfl


noncomputable def standardShellBoundary : frontier squareShell ≃ₜ
    frontier (complementaryRegion squareMiddleBlock) :=
  Homeomorph.setCongr (congrArg frontier complementaryRegion_squareMiddleBlock.symm)



noncomputable def standardDiskProduct {width : ℝ}
    (hwidth : 0 < width) (hsmall : width ≤ (1 / 4 : ℝ)) :
    HamiltonMarkedDiskProduct standardShellBoundary where
  width := width
  width_pos := hwidth
  width_le := hsmall
  map := standardMeridianBandMap
  piecewiseAffine := (standardMeridianBandMap_product_properties hwidth hsmall).1
  injective := (standardMeridianBandMap_product_properties hwidth hsmall).2.1
  inside := by
    rw [complementaryRegion_squareMiddleBlock]
    exact (standardMeridianBandMap_product_properties hwidth hsmall).2.2.1
  proper := by
    rw [complementaryRegion_squareMiddleBlock]
    exact (standardMeridianBandMap_product_properties hwidth hsmall).2.2.2.1
  lateral := by
    intro x t ht hx
    rfl
  open_strip := by
    exact (standardMeridianBandMap_product_properties hwidth hsmall).2.2.2.2.1.preimage
      (Homeomorph.setCongr complementaryRegion_squareMiddleBlock).continuous

end PoincareConjecture.M76.HamiltonIndexOne
