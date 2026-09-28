import PoincareConjecture.Proofs.M76.Mathlib.TriangularRoof
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallNormalization










set_option autoImplicit false

open Set Geometry

namespace TriangularRoofModel



theorem roof_le_third (p : ℝ × ℝ) : roof p ≤ 1 / 3 := by
  have h1 : roof p ≤ p.1 := min_le_left _ _
  have h2 : roof p ≤ p.2 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : roof p ≤ 1 - p.1 - p.2 := (min_le_right _ _).trans (min_le_right _ _)
  linarith



theorem roof_eq_third_iff (p : ℝ × ℝ) :
    roof p = 1 / 3 ↔ p = (1 / 3, 1 / 3) := by
  constructor
  · intro h
    have h1 : roof p ≤ p.1 := min_le_left _ _
    have h2 : roof p ≤ p.2 := (min_le_right _ _).trans (min_le_left _ _)
    have h3 : roof p ≤ 1 - p.1 - p.2 := (min_le_right _ _).trans (min_le_right _ _)
    apply Prod.ext <;> change _ = (1 / 3 : ℝ) <;> linarith
  · rintro rfl
    norm_num [roof]

end TriangularRoofModel

namespace Set

open TriangularRoofModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]





theorem IsFinitePLBallPair.exists_roof {d b : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d b) :
    ∃ r : E → ℝ, FinitePiecewiseAffineOn r d ∧
      (∀ x ∈ d, 0 ≤ r x ∧ (r x = 0 ↔ x ∈ b)) ∧
      ∃ p ∈ d \ b, r p = 1 / 3 ∧
        ∀ x ∈ d, r x ≤ 1 / 3 ∧ (r x = 1 / 3 ↔ x = p) := by
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
    p, ⟨p.property, ?_⟩, hp, fun x hx => ⟨roof_le_third _, ?_⟩⟩
  · intro hb
    have hz := (hzero p p.property).mpr hb
    linarith
  · constructor
    · intro hxmax
      have hgcenter : g x = (1 / 3, 1 / 3) := (roof_eq_third_iff _).mp hxmax
      have heq : e ⟨x, hx⟩ = ⟨(1 / 3, 1 / 3), hcenter⟩ := by
        apply Subtype.ext
        rw [heval]
        exact hgcenter
      have hxp : (⟨x, hx⟩ : d) = p := by
        apply e.injective
        exact heq.trans (e.apply_symm_apply _).symm
      exact congrArg Subtype.val hxp
    · rintro rfl
      exact hp

end Set
