import PoincareConjecture.Proofs.M76.Mathlib.PositiveCollarConnected
import PoincareConjecture.Proofs.M76.Mathlib.CircularSubsetTopology
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCircle
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology

set_option autoImplicit false

open Set

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
  [FiniteDimensional ℝ E]

theorem pointed_collar_cut_side (P : Polygon E (n + 3))
    (hPe : P.HasSimplicialEdges) (hPi : Function.Injective P)
    {B T s₀ s₁ : Set E} {upper A : E → ℝ}
    (C : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)} ≃ₜ T)
    (hheight : ∀ p, A (C p) = (p : E × ℝ).2)
    (hbottom : ∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).2 = 0 → (C p : E) = (p : E × ℝ).1)
    (hbB : P.boundary ℝ ⊆ B) (hu : Geometry.FinitePiecewiseAffineOn upper B)
    (q : E) (hqzero : upper q = 0)
    (hpos : ∀ x ∈ P.boundary ℝ, x ≠ q → 0 < upper x)
    (hs₀ : IsFinitePLBallPair (ℝ × ℝ) s₀ (P.boundary ℝ))
    (hs₁ : IsFinitePLBallPair (ℝ × ℝ) s₁ (P.boundary ℝ))
    (hcover : T ⊆ s₀ ∪ s₁) (hinter : s₀ ∩ s₁ = P.boundary ℝ)
    (hbzero : P.boundary ℝ ⊆ {x | A x = 0}) :
    (∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).1 ∈ P.boundary ℝ →
        (C p : E) ∈ s₀ ∧ ((C p : E) ∈ s₁ ↔ (p : E × ℝ).2 = 0)) ∨
    (∀ p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)},
      (p : E × ℝ).1 ∈ P.boundary ℝ →
        (C p : E) ∈ s₁ ∧ ((C p : E) ∈ s₀ ↔ (p : E × ℝ).2 = 0)) := by
  obtain ⟨e⟩ := P.nonempty_boundary_homeomorph_circle hPe hPi
  have hpre := (isConnected_sdiff_singleton_of_homeomorph_circle (P.boundary ℝ) e q).isPreconnected
  have hsB : P.boundary ℝ \ {q} ⊆ B := sdiff_subset.trans hbB
  have hpositive : ∀ x ∈ P.boundary ℝ \ {q}, 0 < upper x :=
    fun x hx => hpos x hx.1 hx.2
  have hside := C.positive_collar_subset_cut_side hheight hpre hsB
    (hu.continuousOn.mono hsB) hpositive hs₀.isCompact.isClosed hs₁.isCompact.isClosed
    hcover (hinter.subset.trans hbzero)
  have hpunctured (p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)})
      (hp : (p : E × ℝ).1 ∈ P.boundary ℝ) (hz : 0 < (p : E × ℝ).2) :
      (p : E × ℝ).1 ∈ P.boundary ℝ \ {q} := by
    refine ⟨hp, ?_⟩
    intro heq
    have hle := p.property.2.2
    rw [show (p : E × ℝ).1 = q from heq, hqzero] at hle
    exact (not_le_of_gt hz) hle
  have hbottomBoth (p : {p : E × ℝ | p.1 ∈ B ∧ p.2 ∈ Icc 0 (upper p.1)})
      (hp : (p : E × ℝ).1 ∈ P.boundary ℝ) (hz : (p : E × ℝ).2 = 0) :
      (C p : E) ∈ s₀ ∩ s₁ := by
    rw [hbottom p hz]
    exact hinter.symm.subset hp
  rcases hside with h | h
  · left
    intro p hp
    by_cases hz : (p : E × ℝ).2 = 0
    · exact ⟨(hbottomBoth p hp hz).1, iff_of_true (hbottomBoth p hp hz).2 hz⟩
    · have hpz := lt_of_le_of_ne p.property.2.1 (Ne.symm hz)
      have hm := h p (hpunctured p hp hpz) hpz
      exact ⟨hm.1, iff_of_false hm.2 hz⟩
  · right
    intro p hp
    by_cases hz : (p : E × ℝ).2 = 0
    · exact ⟨(hbottomBoth p hp hz).2, iff_of_true (hbottomBoth p hp hz).1 hz⟩
    · have hpz := lt_of_le_of_ne p.property.2.1 (Ne.symm hz)
      have hm := h p (hpunctured p hp hpz) hpz
      exact ⟨hm.1, iff_of_false hm.2 hz⟩

end Polygon
