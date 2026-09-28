import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Order.DenselyOrdered

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Corner

abbrev E3 := EuclideanSpace Real (Fin 3)
abbrev Coordinates := Real × (Real × Real)

def straighten : Diffeomorph (𝓡 3) 𝓘(Real, Coordinates) E3 Coordinates ∞ where
  toFun p := (p 0, p 1, p 2 + (p 0)^2 - (p 1)^2)
  invFun q := WithLp.toLp 2 ![q.1, q.2.1, q.2.2 - q.1^2 + q.2.1^2]
  left_inv p := by
    ext i
    fin_cases i
    · rfl
    · rfl
    · change p 2 + (p 0)^2 - (p 1)^2 - (p 0)^2 + (p 1)^2 = p 2
      ring
  right_inv q := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · simp
        ring
  contMDiff_toFun := by
    apply ContDiff.contMDiff
    have hc (i : Fin 3) : ContDiff Real ∞ (fun p : E3 => p i) :=
      (EuclideanSpace.proj (𝕜 := Real) i).contDiff
    exact (hc 0).prodMk ((hc 1).prodMk (((hc 2).add ((hc 0).pow 2)).sub ((hc 1).pow 2)))
  contMDiff_invFun := by
    apply ContDiff.contMDiff
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact contDiff_fst
    · exact contDiff_fst.comp contDiff_snd
    · exact ((contDiff_snd.comp contDiff_snd).sub (contDiff_fst.pow 2)).add
        ((contDiff_fst.comp contDiff_snd).pow 2)

def body : Set E3 := {p | (p 1)^2 - (p 0)^2 ≤ p 2}

def leftBody : Set E3 := {p | p 0 ≤ 0 ∧ (p 1)^2 - (p 0)^2 ≤ p 2}

def rightBody : Set E3 := {p | 0 ≤ p 0 ∧ (p 1)^2 - (p 0)^2 ≤ p 2}

theorem body_eq_preimage :
    body = straighten ⁻¹' ((univ : Set Real) ×ˢ (univ ×ˢ Ici 0)) := by
  ext p
  change (p 1)^2 - (p 0)^2 ≤ p 2 ↔ True ∧ True ∧ 0 ≤ p 2 + (p 0)^2 - (p 1)^2
  simp only [true_and]
  constructor <;> intro h <;> nlinarith

theorem leftBody_eq_preimage :
    leftBody = straighten ⁻¹' (Iic 0 ×ˢ ((univ : Set Real) ×ˢ Ici 0)) := by
  ext p
  change (p 0 ≤ 0 ∧ (p 1)^2 - (p 0)^2 ≤ p 2) ↔
    p 0 ≤ 0 ∧ True ∧ 0 ≤ p 2 + (p 0)^2 - (p 1)^2
  simp only [true_and]
  exact and_congr_right (fun _ => by constructor <;> intro h <;> linarith)

theorem rightBody_eq_preimage :
    rightBody = straighten ⁻¹' (Ici 0 ×ˢ ((univ : Set Real) ×ˢ Ici 0)) := by
  ext p
  change (0 ≤ p 0 ∧ (p 1)^2 - (p 0)^2 ≤ p 2) ↔
    0 ≤ p 0 ∧ True ∧ 0 ≤ p 2 + (p 0)^2 - (p 1)^2
  simp only [true_and]
  exact and_congr_right (fun _ => by constructor <;> intro h <;> linarith)

theorem sides_union : leftBody ∪ rightBody = body := by
  ext p
  change (p 0 ≤ 0 ∧ _ ∨ 0 ≤ p 0 ∧ _) ↔ _
  constructor
  · rintro (h | h) <;> exact h.2
  · intro h
    rcases le_total (p 0) 0 with hx | hx
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩

theorem sides_inter :
    leftBody ∩ rightBody = {p : E3 | p 0 = 0 ∧ (p 1)^2 ≤ p 2} := by
  ext p
  constructor
  · rintro ⟨hl, hr⟩
    have hx : p 0 = 0 := le_antisymm hl.1 hr.1
    exact ⟨hx, by simpa [hx] using hl.2⟩
  · rintro ⟨hx, hz⟩
    exact ⟨⟨hx.le, by simpa [hx] using hz⟩,
      ⟨hx.ge, by simpa [hx] using hz⟩⟩

theorem interior_body :
    interior body = {p : E3 | (p 1)^2 - (p 0)^2 < p 2} := by
  rw [body_eq_preimage]
  change interior (straighten.toHomeomorph ⁻¹'
    ((univ : Set Real) ×ˢ (univ ×ˢ Ici 0))) = _
  rw [← straighten.toHomeomorph.preimage_interior]
  simp only [interior_prod_eq, interior_univ, interior_Ici]
  ext p
  change (True ∧ True ∧ 0 < p 2 + (p 0)^2 - (p 1)^2) ↔ _
  simp only [true_and]
  change (0 < p 2 + (p 0)^2 - (p 1)^2) ↔
    ((p 1)^2 - (p 0)^2 < p 2)
  constructor <;> intro h <;> nlinarith

theorem wall_above_graph_mem_interior_union {p : E3}
    (hx : p 0 = 0) (hz : (p 1)^2 < p 2) :
    p ∈ interior (leftBody ∪ rightBody) := by
  rw [sides_union, interior_body]
  simpa [hx] using hz

end Poincare.Manifold.Schoenflies.Saddle.Wall.Corner
