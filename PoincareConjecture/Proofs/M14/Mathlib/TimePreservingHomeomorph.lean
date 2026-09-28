import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FiniteDimensional

set_option autoImplicit false

open Set
open scoped NNReal

namespace PoincareConjecture.M14

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

set_option backward.isDefEq.respectTransparency false in

theorem exists_timePreserving_homeomorph_extension
    {f : E × ℝ → F × ℝ} {L : (E × ℝ) ≃L[ℝ] (F × ℝ)}
    {S : Set (E × ℝ)} {c : ℝ≥0}
    (hf : ApproximatesLinearOn f (L : (E × ℝ) →L[ℝ] (F × ℝ)) S c)
    (hft : ∀ z ∈ S, (f z).2 = z.2) (hLt : ∀ z, (L z).2 = z.2)
    (hc : lipschitzExtensionConstant F * c <
      ‖(L.symm : (F × ℝ) →L[ℝ] (E × ℝ))‖₊⁻¹) :
    ∃ g : (E × ℝ) ≃ₜ (F × ℝ), EqOn f g S ∧ ∀ z, (g z).2 = z.2 := by
  have hsp : LipschitzOnWith c (fun z => (f z - L z).1) S := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro z hz w hw
    exact (norm_fst_le ((f z - L z) - (f w - L w))).trans
      ((lipschitzOnWith_iff_norm_sub_le.mp hf.lipschitzOnWith) hz hw)
  obtain ⟨u, hu, heq⟩ := hsp.extend_finite_dimension
  let g : E × ℝ → F × ℝ := fun z => L z + (u z, 0)
  have hgf : EqOn f g S := by
    intro z hz
    apply Prod.ext
    · change (f z).1 = (L z).1 + u z
      rw [← heq hz]
      change (f z).1 = (L z).1 + ((f z).1 - (L z).1)
      abel
    · change (f z).2 = (L z).2 + 0
      rw [add_zero, hft z hz, hLt z]
  have herror : LipschitzWith (lipschitzExtensionConstant F * c)
      (fun z => (u z, (0 : ℝ))) := by
    simpa only [max_eq_left (zero_le : 0 ≤ lipschitzExtensionConstant F * c)] using
      hu.prodMk (LipschitzWith.const (0 : ℝ))
  have hg : ApproximatesLinearOn g (L : (E × ℝ) →L[ℝ] (F × ℝ)) univ
      (lipschitzExtensionConstant F * c) := by
    apply LipschitzOnWith.approximatesLinearOn
    rw [lipschitzOnWith_univ]
    convert! herror using 1
    funext z
    exact add_sub_cancel_left (L z) (u z, 0)
  let : FiniteDimensional ℝ (E × ℝ) := L.symm.finiteDimensional
  exact ⟨hg.toHomeomorph g (Or.inr hc), hgf, fun z => by
    change (L z).2 + 0 = z.2
    rw [add_zero, hLt z]⟩

end PoincareConjecture.M14
