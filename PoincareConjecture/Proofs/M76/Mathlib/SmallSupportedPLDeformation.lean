import PoincareConjecture.Proofs.M76.Mathlib.FinitePLLipschitz
import PoincareConjecture.Proofs.M76.Mathlib.ZeroExtensionLipschitz
import PoincareConjecture.Proofs.M76.Mathlib.SmallLipschitzHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLHomeomorph











set_option autoImplicit false

open Set Geometry
open scoped NNReal

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem FinitePiecewiseAffineOn.exists_small_supported_deformation
    {f : E → E} {C : Set E} (hf : FinitePiecewiseAffineOn f C) (hcv : Convex ℝ C)
    (hzero : ∀ x ∈ frontier C, f x = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| ≤ ε →
      ∃ H : E ≃ₜ E, (∀ x ∈ C, H x = x + t • f x) ∧
        (∀ x, x ∉ interior C → H x = x) ∧ H '' C = C ∧
        ∃ e : C ≃ₜ C, e.IsFinitePL ∧ ∀ x : C, (e x : E) = H x := by
  classical
  have hfcopy := hf
  obtain ⟨K, hK, hKC, hfaces⟩ := hfcopy
  have hCc : IsClosed C := by
    rw [← hKC]
    exact (K.isCompact_space_of_finite hK).isClosed
  obtain ⟨L, hL⟩ := hf.exists_lipschitzOnWith hcv
  have hu := hL.indicator_of_eq_zero_frontier hCc hzero
  let ε : ℝ := ((L : ℝ) + 1)⁻¹ / 2
  have hpos : 0 < (L : ℝ) + 1 := by positivity
  have hε : 0 < ε := div_pos (inv_pos.mpr hpos) (by norm_num)
  have heq : ε * ((L : ℝ) + 1) = 1 / 2 := by
    dsimp [ε]
    field_simp
  have hεL : ε * (L : ℝ) < 1 := by nlinarith
  refine ⟨ε, hε, fun t ht => ?_⟩
  have hsmall : ‖t‖₊ * L < 1 := by
    apply NNReal.coe_lt_coe.mp
    simp only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, NNReal.coe_one]
    exact (mul_le_mul_of_nonneg_right ht L.coe_nonneg).trans_lt hεL
  have hscale : LipschitzWith (‖t‖₊ * L) (fun x => t • C.indicator f x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, ← smul_sub, norm_smul, NNReal.coe_mul, coe_nnnorm, dist_eq_norm]
    exact (mul_le_mul_of_nonneg_left (hu.norm_sub_le x y) (norm_nonneg t)).trans_eq
      (mul_assoc _ _ _).symm
  obtain ⟨H, hH⟩ := hscale.exists_homeomorph_add hsmall
  have hformula (x : E) (hx : x ∈ C) : H x = x + t • f x := by
    rw [hH, indicator_of_mem hx]
  have hfix (x : E) (hx : x ∉ interior C) : H x = x := by
    have hz : C.indicator f x = 0 := by
      by_cases hxC : x ∈ C
      · rw [indicator_of_mem hxC]
        exact hzero x ⟨subset_closure hxC, hx⟩
      · exact indicator_of_notMem hxC f
    rw [hH, hz, smul_zero, add_zero]
  have hmem (x : E) : H x ∈ C ↔ x ∈ C := by
    constructor
    · intro hx
      by_contra hn
      rw [hfix x (fun hi => hn (interior_subset hi))] at hx
      exact hn hx
    · intro hx
      by_contra hn
      have he : H x = x := H.injective (hfix (H x) (fun hi => hn (interior_subset hi)))
      exact hn (he.symm ▸ hx)
  have himage : H '' C = C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hmem y).mpr hy
    · intro hx
      refine ⟨H.symm x, (hmem (H.symm x)).mp ?_, H.apply_symm_apply x⟩
      rwa [H.apply_symm_apply]
  let e : C ≃ₜ C := (H.image C).trans (Homeomorph.setCongr himage)
  refine ⟨H, hformula, hfix, himage, e, ?_, fun _ => rfl⟩
  refine ⟨fun x => x + t • f x, ⟨K, hK, hKC, ?_⟩, fun x => hformula x x.property⟩
  intro s hs
  obtain ⟨a, ha⟩ := hfaces s hs
  refine ⟨ContinuousAffineMap.id ℝ E + t • a, ?_⟩
  intro x hx
  change x + t • f x = x + t • a x
  rw [ha hx]

end Geometry
