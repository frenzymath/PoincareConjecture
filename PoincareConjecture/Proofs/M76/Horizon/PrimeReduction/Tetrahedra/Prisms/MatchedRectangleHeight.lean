import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.PrescribedRectangleSides
import PoincareConjecture.Proofs.M76.Mathlib.RectangleConnectedSides
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLProductBandGluing









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.PrismBelt

local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

def sidePoint (b : Bool) (t : I) : Square :=
  ⟨((if b then 1 else 0), t), by cases b <;> exact ⟨by norm_num, t.property⟩⟩

theorem exists_matched_rectangle_height
    {E ι κ : Type*} [TopologicalSpace E]
    (M : ι → Set E) (L : κ → Set E) (ends : ι → Bool → κ)
    (G : ∀ i, Square ≃ₜ M i) (e : ∀ k, I ≃ₜ L k)
    (hside : ∀ i b t, (G i (sidePoint b t) : E) = e (ends i b) t)
    (hcontact : ∀ i j, i ≠ j → (M i ∩ M j).Nonempty →
      ∃ b c, ends i b = ends j c ∧ M i ∩ M j = L (ends i b)) :
    ∃ A : E → ℝ, ∀ i p, A (G i p) = (p : ℝ × ℝ).2 := by
  classical
  have hinverse (i : ι) (b : Bool) (x : E) (hx : x ∈ M i) (hxl : x ∈ L (ends i b)) :
      ((G i).symm ⟨x, hx⟩ : ℝ × ℝ).2 = ((e (ends i b)).symm ⟨x, hxl⟩ : ℝ) := by
    let t := (e (ends i b)).symm ⟨x, hxl⟩
    have he : G i (sidePoint b t) = ⟨x, hx⟩ := Subtype.ext
      ((hside i b t).trans (congrArg Subtype.val ((e (ends i b)).apply_symm_apply _)))
    rw [← he, (G i).symm_apply_apply]
    rfl
  have hagree (i j : ι) (x : E) (hi : x ∈ M i) (hj : x ∈ M j) :
      ((G i).symm ⟨x, hi⟩ : ℝ × ℝ).2 = ((G j).symm ⟨x, hj⟩ : ℝ × ℝ).2 := by
    by_cases hij : i = j
    · subst j
      rfl
    obtain ⟨b, c, he, hmeet⟩ := hcontact i j hij ⟨x, hi, hj⟩
    have hxi := hmeet.subset ⟨hi, hj⟩
    have hxj : x ∈ L (ends j c) := he ▸ hxi
    rw [hinverse i b x hi hxi, hinverse j c x hj hxj]
    have hh (k l : κ) (hkl : k = l) (hk : x ∈ L k) (hl : x ∈ L l) :
        ((e k).symm ⟨x, hk⟩ : ℝ) = ((e l).symm ⟨x, hl⟩ : ℝ) := by
      subst l
      rfl
    exact hh _ _ he hxi hxj
  let A : E → ℝ := fun x => if hx : ∃ i, x ∈ M i then
    ((G hx.choose).symm ⟨x, hx.choose_spec⟩ : ℝ × ℝ).2 else 0
  refine ⟨A, ?_⟩
  intro i p
  have hx : ∃ j, (G i p : E) ∈ M j := ⟨i, (G i p).property⟩
  change (if hx : ∃ j, (G i p : E) ∈ M j then _ else _) = _
  rw [dif_pos hx, hagree hx.choose i (G i p) hx.choose_spec (G i p).property]
  exact congrArg (fun z : Square => (z : ℝ × ℝ).2) ((G i).symm_apply_apply p)

end PoincareConjecture.M76.PrismBelt
