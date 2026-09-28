import Mathlib.Analysis.Fourier.AddCircle

set_option autoImplicit false

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def periodicTranslation (a : ℝ) :
    C(AddCircle L, E) ≃ₗᵢ[ℝ] C(AddCircle L, E) where
  toFun f := ⟨fun x => f (x - (a : AddCircle L)),
    f.continuous.comp (continuous_id.sub continuous_const)⟩
  invFun f := ⟨fun x => f (x + (a : AddCircle L)),
    f.continuous.comp (continuous_id.add continuous_const)⟩
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl
  norm_map' f := by
    apply le_antisymm
    · exact (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
        (fun x => ContinuousMap.norm_coe_le_norm f _)
    · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
      intro x
      simpa using ContinuousMap.norm_coe_le_norm
        (⟨fun y => f (y - (a : AddCircle L)),
          f.continuous.comp (continuous_id.sub continuous_const)⟩ : C(AddCircle L, E))
        (x + (a : AddCircle L))

theorem continuous_periodicTranslation :
    Continuous (fun p : ℝ × C(AddCircle L, E) => periodicTranslation p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.comp (continuous_fst.snd.prodMk
    (continuous_snd.sub ((AddCircle.continuous_mk' L).comp continuous_fst.fst)))

end PoincareConjecture.M63
