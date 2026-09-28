import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.PeriodicWindows
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Boundary.Upper.ProjectedCrossing



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.PeriodicSquare

local notation "P2" => (ℝ × ℝ)

theorem SourceSquareMap.exists_original_translated_window_patches
    {E V X ι I J : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace X] {e : ι → OpenPartialHomeomorph X V}
    {p : ℝ} [Fact (0 < p)] {K : SimplicialComplex ℝ E} {S : Set X}
    (M : SourceSquareMap p K) (H : K.space ≃ₜ S)
    (F : E → X) (hF : PolyhedralPLInCharts e F K.space)
    (hFval : ∀ x : K.space, F x = (H x : X))
    (h : (AddCircle p × AddCircle p) ≃ₜ S)
    (hvalue : ∀ z : Square p, h (projection p z) = H (M.map z))
    [Finite I] [Finite J] (a b : I → P2) (c d : J → P2)
    (hcd : ∀ j, c j ≠ d j)
    (hselfA : ∀ i k, i ≠ k →
      segment ℝ (a i) (b i) ∩ segment ℝ (a k) (b k) ⊆ {a i, b i})
    (hselfB : ∀ j k, j ≠ k →
      segment ℝ (c j) (d j) ∩ segment ℝ (c k) (d k) ⊆ {c j, d j})
    (C₀ C₁ : Set (AddCircle p × AddCircle p))
    (hwindow₀ : ∀ z ∈ Icc (-p) (2 * p) ×ˢ Icc (-p) (2 * p),
      ((z.1 : AddCircle p), (z.2 : AddCircle p)) ∈ C₀ ↔
        z ∈ ⋃ i, segment ℝ (a i) (b i))
    (hwindow₁ : ∀ z ∈ Icc (-p) (2 * p) ×ˢ Icc (-p) (2 * p),
      ((z.1 : AddCircle p), (z.2 : AddCircle p)) ∈ C₁ ↔
        z ∈ ⋃ j, segment ℝ (c j) (d j)) :
    ∃ v : P2, ‖v‖ < p / 4 ∧
      (((fun q => (h q : X)) '' C₀) ∩
        (fun q => (h q : X)) '' ((fun q => q + ((v.1 : AddCircle p), (v.2 : AddCircle p))) '' C₁)).Finite ∧
      ∀ x ∈ ((fun q => (h q : X)) '' C₀) ∩
        (fun q => (h q : X)) '' ((fun q => q + ((v.1 : AddCircle p), (v.2 : AddCircle p))) '' C₁),
        ∃ δ : ℝ, 0 < δ ∧ ∃ u : P2 → X,
          PolyhedralPLInCharts e u (Icc (-δ) δ ×ˢ Icc (-δ) δ) ∧
          InjOn u (Icc (-δ) δ ×ˢ Icc (-δ) δ) ∧
          MapsTo u (Icc (-δ) δ ×ˢ Icc (-δ) δ) S ∧ u 0 = x ∧
          (∀ z ∈ Icc (-δ) δ ×ˢ Icc (-δ) δ,
            u z ∈ (fun q => (h q : X)) '' C₀ ↔ z.2 = 0) ∧
          ∀ z ∈ Icc (-δ) δ ×ˢ Icc (-δ) δ,
            u z ∈ (fun q => (h q : X)) ''
              ((fun q => q + ((v.1 : AddCircle p), (v.2 : AddCircle p))) '' C₁) ↔ z.1 = 0 := by
  let k (q : AddCircle p × AddCircle p) : X := h q
  have hki : Function.Injective k := by
    intro q r heq
    exact h.injective (Subtype.ext heq)
  have hmem (q : AddCircle p × AddCircle p) (D : Set (AddCircle p × AddCircle p)) :
      k q ∈ k '' D ↔ q ∈ D := by
    constructor
    · rintro ⟨r, hr, heq⟩
      exact hki heq ▸ hr
    · intro hq
      exact ⟨q, hq, rfl⟩
  obtain ⟨v, hv, hfinite, hcharts⟩ :=
    exists_small_translation_periodic_window_charts a b c d hcd hselfA hselfB
      C₀ C₁ hwindow₀ hwindow₁
  let D := (fun q => q + ((v.1 : AddCircle p), (v.2 : AddCircle p))) '' C₁
  have hpre (x : X) (hx : x ∈ k '' C₀ ∩ k '' D) :
      ∃ q ∈ C₀ ∩ D, k q = x := by
    obtain ⟨q, hq, rfl⟩ := hx.1
    exact ⟨q, ⟨hq, (hmem q D).mp hx.2⟩, rfl⟩
  refine ⟨v, hv, ?_, ?_⟩
  · exact (hfinite.image k).subset (fun x hx => hpre x hx)
  · intro x hx
    obtain ⟨q, hq, hqx⟩ := hpre x hx
    obtain ⟨A, U, hU, hA0U, hA0q, haxis₀, haxis₁⟩ := hcharts q hq
    obtain ⟨δ, hδ, u, hu, hui, huS, hu0, huaxis₀, huaxis₁⟩ :=
      M.exists_original_projected_crossing_patch H F hF hFval h hvalue A hU hA0U
        (C₀ := k '' C₀) (C₁ := k '' D)
        (fun z hz => (hmem _ C₀).trans (haxis₀ z hz))
        (fun z hz => (hmem _ D).trans (haxis₁ z hz))
    refine ⟨δ, hδ, u, hu, hui, huS, ?_, huaxis₀, huaxis₁⟩
    exact hu0.trans ((congrArg k hA0q).trans hqx)

end PoincareConjecture.M76.PeriodicSquare
