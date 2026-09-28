import PoincareConjecture.Proofs.M76.Mathlib.TaperedAffineRoof

set_option autoImplicit false

open Set Geometry

namespace AffineMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_singleVertex_source_roof (A : E →ᵃ[ℝ] ℝ)
    {s : Finset E} {q : E} {β : ℝ} (hβ : 0 < β) {S : Set (E × ℝ)}
    (hsource : (q ∉ s ∧ S = (convexHull ℝ (s : Set E) ∩ {x | A x = 0}) ×ˢ Icc 0 β) ∨
      ∃ w : E, q ∈ s ∧ q ≠ w ∧ w ∈ convexHull ℝ ((s : Set E) \ {q}) ∧
        (convexHull ℝ (s : Set E) ∩ {x | A x = 0} = segment ℝ q w) ∧
        S = TaperedStrip.segmentDomain q w β) :
    ∃ a : E →ᴬ[ℝ] ℝ,
      (∀ x ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0}, a x ∈ Icc 0 β) ∧
      S = {p : E × ℝ | p.1 ∈ convexHull ℝ (s : Set E) ∩ {x | A x = 0} ∧
        p.2 ∈ Icc 0 (a p.1)} ∧
      ((q ∉ s ∧ a = ContinuousAffineMap.const ℝ E β) ∨
        ∃ w : E, q ∈ s ∧ q ≠ w ∧ w ∈ convexHull ℝ ((s : Set E) \ {q}) ∧
          (convexHull ℝ (s : Set E) ∩ {x | A x = 0} = segment ℝ q w) ∧
          a q = 0 ∧ a w = β) := by
  rcases hsource with ⟨hqs, hS⟩ | ⟨w, hqs, hqw, hw, hsec, hS⟩
  · exact ⟨ContinuousAffineMap.const ℝ E β, fun _ _ => ⟨hβ.le, le_rfl⟩,
      hS, Or.inl ⟨hqs, rfl⟩⟩
  · obtain ⟨a, haq, haw, hbound, hband⟩ := TaperedStrip.exists_affine_segmentDomain_roof hqw hβ
    refine ⟨a, fun x hx => hbound x (hsec ▸ hx), ?_,
      Or.inr ⟨w, hqs, hqw, hw, hsec, haq, haw⟩⟩
    rw [hS, hsec]
    exact hband

end AffineMap
