import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedBallExtension
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedInterval

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.Dehn.Annuli

theorem exists_disk_homeomorph_prescribed_arc
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {D U W : Set E} {B V Z : Set F} {a b : E} {c d : F}
    (hD : IsFinitePLBallPair (ℝ × ℝ) D (U ∪ W))
    (hB : IsFinitePLBallPair (ℝ × ℝ) B (V ∪ Z))
    (hU : IsFinitePLBallPair ℝ U {a, b}) (hW : IsFinitePLBallPair ℝ W {a, b})
    (hV : IsFinitePLBallPair ℝ V {c, d})
    (hUW : U ∩ W = {a, b}) (hVZ : V ∩ Z = {c, d})
    (r : W ≃ₜ Z) (hr : r.IsFinitePL)
    (hra : (r ⟨a, hW.1 (by simp)⟩ : F) = c)
    (hrb : (r ⟨b, hW.1 (by simp)⟩ : F) = d) :
    ∃ H : D ≃ₜ B, H.IsFinitePL ∧
      (∀ x : W, (H ⟨x, hD.1 (Or.inr x.property)⟩ : F) = r x) ∧
      (∀ x : D, (x : E) ∈ U ↔ (H x : F) ∈ V) ∧
      ∀ x : D, (x : E) ∈ W ↔ (H x : F) ∈ Z := by
  have hends (x : W) : (x : E) ∈ ({a, b} : Set E) ↔
      (r x : F) ∈ ({c, d} : Set F) := by
    simp only [mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro (hx | hx)
      · exact Or.inl ((congrArg (fun z : W ↦ (r z : F)) (Subtype.ext hx)).trans hra)
      · exact Or.inr ((congrArg (fun z : W ↦ (r z : F)) (Subtype.ext hx)).trans hrb)
    · rintro (hx | hx)
      · exact Or.inl (congrArg Subtype.val (r.injective (Subtype.ext (hx.trans hra.symm))))
      · exact Or.inr (congrArg Subtype.val (r.injective (Subtype.ext (hx.trans hrb.symm))))
  obtain ⟨H, hH, hHr, hHU, hHW⟩ :=
    hD.exists_extension_of_boundary_piece hB hU hV hUW hVZ r hr hends
  exact ⟨H, hH, fun x ↦ congrArg Subtype.val (hHr x), hHU, hHW⟩

end PoincareConjecture.M76.Dehn.Annuli
