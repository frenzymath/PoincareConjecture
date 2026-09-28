import PoincareConjecture.Proofs.M76.Mathlib.RegularTriangleEdgeCollar

set_option autoImplicit false

open Set Geometry

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_regular_triangle_collar (A : E →ᵃ[ℝ] ℝ) {s : Finset E}
    (hi : AffineIndependent ℝ ((↑) : s → E)) (hs : s.card = 3) {α β : ℝ}
    (hαβ : α < β) (hreg : ∀ z ∈ s, A z < α ∨ β < A z)
    (hmeet : (convexHull ℝ (s : Set E) ∩ {x | A x ∈ Icc α β}).Nonempty) :
    ∃ H : ((convexHull ℝ (s : Set E) ∩ {x | A x = α}) ×ˢ Icc α β : Set (E × ℝ)) ≃ₜ
        (convexHull ℝ (s : Set E) ∩ {x | A x ∈ Icc α β} : Set E),
      H.IsFinitePL ∧
      (∀ p, A (H p) = (p : E × ℝ).2) ∧
      (∀ (x : E) (hx : x ∈ convexHull ℝ (s : Set E) ∩ {x | A x = α}),
        (H ⟨(x, α), ⟨hx, ⟨le_rfl, hαβ.le⟩⟩⟩ : E) = x) ∧
      ∀ (e : Finset E), e.card = 2 → e ⊆ s →
        ∀ p : ((convexHull ℝ (s : Set E) ∩ {x | A x = α}) ×ˢ Icc α β : Set (E × ℝ)),
          (p : E × ℝ).1 ∈ convexHull ℝ (e : Set E) ↔
            (H p : E) ∈ convexHull ℝ (e : Set E) := by
  classical
  obtain ⟨v, u, w, hlabels, hvu, hvw, huw, hside⟩ := A.exists_regular_triangle_apex hs hreg hmeet
  have hvec : Function.Injective ![v, u, w] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have hrange : range ![v, u, w] ⊆ (s : Set E) := by
    rintro z ⟨i, rfl⟩
    rw [hlabels]
    fin_cases i <;> simp
  have hind : AffineIndependent ℝ ![v, u, w] := (hi.mono hrange).of_set_of_injective hvec
  obtain ⟨hsection, hlocal⟩ := A.exists_triangle_segment_edge_collar hind hαβ hside
  rw [← hsection] at hlocal
  subst s
  have hset : (({v, u, w} : Finset E) : Set E) = {v, u, w} := by simp
  rw [hset]
  exact hlocal

end AffineMap
