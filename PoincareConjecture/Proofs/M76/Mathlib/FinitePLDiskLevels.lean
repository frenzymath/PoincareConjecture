import PoincareConjecture.Proofs.M76.Mathlib.TriangularRoofLevels
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallPreimages










set_option autoImplicit false

open Set Geometry TriangularRoofModel

namespace Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem IsFinitePLBallPair.exists_roof_with_disk_levels {d b : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) :
    ∃ r : E → ℝ, FinitePiecewiseAffineOn r d ∧
      (∀ x ∈ d, 0 ≤ r x ∧ (r x = 0 ↔ x ∈ b)) ∧
      (∃ p ∈ d \ b, r p = 1 / 3 ∧
        ∀ x ∈ d, r x ≤ 1 / 3 ∧ (r x = 1 / 3 ↔ x = p)) ∧
      ∀ t : ℝ, 0 ≤ t → t < 1 / 3 →
        IsFinitePLBallPair (ℝ × ℝ) (d ∩ {x | t ≤ r x}) (d ∩ {x | r x = t}) := by
  classical
  obtain ⟨e, he, heb⟩ := hd.exists_homeomorph isFinitePLBallPair_base
  obtain ⟨g, hg, heval⟩ := he
  have hmap : MapsTo g d base := by
    intro x hx
    rw [← heval ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).property
  let r : E → ℝ := roof ∘ g
  have hr : FinitePiecewiseAffineOn r d := finitePiecewiseAffineOn_roof.comp hg hmap
  have hzero (x : E) (hx : x ∈ d) : r x = 0 ↔ x ∈ b := by
    have hb := heb ⟨x, hx⟩
    rw [heval, frontier_base] at hb
    exact hb.symm
  have hcenter : ((1 / 3, 1 / 3) : ℝ × ℝ) ∈ base :=
    (roof_nonneg_iff _).mp (by norm_num [roof])
  let p : d := e.symm ⟨(1 / 3, 1 / 3), hcenter⟩
  have hp : r p = 1 / 3 := by
    change roof (g p) = 1 / 3
    rw [← heval p]
    change roof (e (e.symm ⟨(1 / 3, 1 / 3), hcenter⟩)) = 1 / 3
    rw [e.apply_symm_apply]
    norm_num [roof]
  refine ⟨r, hr, fun x hx => ⟨(roof_nonneg_iff _).mpr (hmap hx), hzero x hx⟩,
    ⟨p, ⟨p.property, ?_⟩, hp, fun x hx => ⟨roof_le_third _, ?_⟩⟩, ?_⟩
  · intro hb
    have hz := (hzero p p.property).mpr hb
    linarith
  · constructor
    · intro hmax
      have heq : e ⟨x, hx⟩ = ⟨(1 / 3, 1 / 3), hcenter⟩ := by
        apply Subtype.ext
        rw [heval]
        exact (roof_eq_third_iff _).mp hmax
      exact congrArg Subtype.val (e.injective (heq.trans (e.apply_symm_apply _).symm))
    · rintro rfl
      exact hp
  · intro t ht htmax
    exact (show e.IsFinitePL from ⟨g, hg, heval⟩).preimage_ballPair
      (isFinitePLBallPair_roof_superlevel htmax) (roof_superlevel_subset_base ht) heval

end Set
