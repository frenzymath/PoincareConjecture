import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.SourceCircleCuts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.PairedOrientedCollars
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Resolution.ComponentRetention

set_option autoImplicit false
open Set Geometry PLAnnularStrip
open _root_.Dehn

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)

variable {A : Set P2} {l r L d : ℝ}

theorem oriented_collar_boundary_subsets (B : OrientedPolygonCollar l r A) :
    B.outer.boundary ℝ ⊆ A ∧ B.inner.boundary ℝ ⊆ A := by
  constructor
  · intro x hx
    apply B.carrier.symm.subset
    have hf := (B.outer.frontier_closure_inside B.outer_simplicial B.outer_injective).symm ▸ hx
    refine ⟨by simpa using hf.1, ?_⟩
    intro hi
    exact hf.2 ((B.outer.interior_closure_inside B.outer_simplicial B.outer_injective).symm ▸
      B.nested (subset_closure hi))
  · intro x hx
    apply B.carrier.symm.subset
    have hf := (B.inner.frontier_closure_inside B.inner_simplicial B.inner_injective).symm ▸ hx
    have hc : x ∈ closure B.inner.inside := by simpa using hf.1
    exact ⟨subset_closure (B.nested hc), fun hi ↦ hf.2
      ((B.inner.interior_closure_inside B.inner_simplicial B.inner_injective).symm ▸ hi)⟩

theorem oriented_collar_enclosing_iff (B : OrientedPolygonCollar l r A)
    (hA : A ⊆ {p : P2 | -d < depth L p ∧ depth L p < d}) :
    annulusSquare L d ⊆ B.outer.inside ↔ annulusSquare L d ⊆ B.inner.inside := by
  constructor
  · intro ho x hx
    by_contra hi
    have hc : x ∈ A := B.carrier.symm ▸ ⟨subset_closure (ho hx), hi⟩
    exact (not_lt_of_ge ((mem_annulusSquare_iff L d x).mp hx)) (hA hc).2
  · exact fun hi x hx ↦ B.nested (subset_closure (hi hx))

theorem oriented_collar_disk_or_enclosing (B : OrientedPolygonCollar l r A)
    (hA : A ⊆ {p : P2 | -d < depth L p ∧ depth L p < d}) :
    IsFinitePLBallPair P2 (closure B.outer.inside) (B.outer.boundary ℝ) ∧
    IsFinitePLBallPair P2 (closure B.inner.inside) (B.inner.boundary ℝ) ∧
    closure B.outer.inside ⊆ interior (annulusSquare L (-d)) ∧
    (annulusSquare L d ⊆ B.inner.inside ∨
      closure B.outer.inside ⊆ {p : P2 | -d < depth L p ∧ depth L p < d}) := by
  obtain ⟨hball, hout, hcase⟩ := source_polygon_disk_or_enclosing B.outer
    B.outer_simplicial B.outer_injective (fun x hx ↦
      hA ((oriented_collar_boundary_subsets B).1 hx))
  refine ⟨hball, B.inner.isFinitePLBallPair_closed_inside B.inner_simplicial B.inner_injective,
    hout, ?_⟩
  exact hcase.imp ((oriented_collar_enclosing_iff B hA).mp) id

theorem oriented_collar_component_sides (B : OrientedPolygonCollar l r A)
    {U : Set P2} (hU : IsPreconnected U) (havoid : Disjoint U A) :
    U ⊆ B.inner.inside ∨ U ⊆ (closure B.outer.inside)ᶜ := by
  have h := connected_sides_of_disjoint_closed_collar hU isClosed_closure
    (B.nested.trans subset_closure) (by
      simpa only [B.inner.interior_closure_inside B.inner_simplicial B.inner_injective,
        ← B.carrier] using havoid)
  simpa only [B.inner.interior_closure_inside B.inner_simplicial B.inner_injective] using h

theorem disjoint_oriented_collars_source_cases {A₀ A₁ : Set P2} {l₀ r₀ l₁ r₁ : ℝ}
    (B₀ : OrientedPolygonCollar l₀ r₀ A₀) (B₁ : OrientedPolygonCollar l₁ r₁ A₁)
    (hdis : Disjoint A₀ A₁) :
    closure B₁.outer.inside ⊆ B₀.inner.inside ∨
    closure B₀.outer.inside ⊆ B₁.inner.inside ∨
    Disjoint (closure B₀.outer.inside) (closure B₁.outer.inside) := by
  have hb₀ := (oriented_collar_boundary_subsets B₀).1
  have hb₁ := (oriented_collar_boundary_subsets B₁).1
  have hs₀ := oriented_collar_component_sides B₁
    (B₀.outer.isConnected_boundary B₀.outer_simplicial B₀.outer_injective).isPreconnected
    (hdis.mono_left hb₀)
  have hs₁ := oriented_collar_component_sides B₀
    (B₁.outer.isConnected_boundary B₁.outer_simplicial B₁.outer_injective).isPreconnected
    (hdis.symm.mono_left hb₁)
  rcases B₀.outer.closed_inside_nested_or_disjoint B₁.outer
      B₀.outer_simplicial B₀.outer_injective B₁.outer_simplicial B₁.outer_injective
      (hdis.mono hb₀ hb₁) with hn | hn | hd
  · rcases hs₀ with hi | ho
    · exact Or.inr (Or.inl (B₁.inner.closure_inside_subset_inside_of_boundary_subset_inside
        B₀.outer B₁.inner_simplicial B₁.inner_injective
        B₀.outer_simplicial B₀.outer_injective hi))
    · have hx : B₀.outer 0 ∈ closure B₀.outer.inside := by
        exact frontier_subset_closure ((B₀.outer.frontier_inside
          B₀.outer_simplicial B₀.outer_injective).symm ▸ B₀.outer.vertex_mem_boundary 0)
      exact (ho (B₀.outer.vertex_mem_boundary 0) (subset_closure (hn hx))).elim
  · rcases hs₁ with hi | ho
    · exact Or.inl (B₀.inner.closure_inside_subset_inside_of_boundary_subset_inside
        B₁.outer B₀.inner_simplicial B₀.inner_injective
        B₁.outer_simplicial B₁.outer_injective hi)
    · have hx : B₁.outer 0 ∈ closure B₁.outer.inside :=
        frontier_subset_closure ((B₁.outer.frontier_inside
          B₁.outer_simplicial B₁.outer_injective).symm ▸ B₁.outer.vertex_mem_boundary 0)
      exact (ho (B₁.outer.vertex_mem_boundary 0) (subset_closure (hn hx))).elim
  · exact Or.inr (Or.inr hd)

theorem enclosing_oriented_collars_nested {A₀ A₁ : Set P2} {l₀ r₀ l₁ r₁ : ℝ}
    (B₀ : OrientedPolygonCollar l₀ r₀ A₀) (B₁ : OrientedPolygonCollar l₁ r₁ A₁)
    (hdis : Disjoint A₀ A₁) (hwidth : 2 * d < L)
    (h₀ : annulusSquare L d ⊆ B₀.outer.inside)
    (h₁ : annulusSquare L d ⊆ B₁.outer.inside) :
    closure B₁.outer.inside ⊆ B₀.inner.inside ∨
    closure B₀.outer.inside ⊆ B₁.inner.inside := by
  rcases disjoint_oriented_collars_source_cases B₀ B₁ hdis with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · have hx : (d, d) ∈ annulusSquare L d := by
      change (d ≤ d ∧ d ≤ L - d) ∧ (d ≤ d ∧ d ≤ L - d)
      constructor <;> exact ⟨le_rfl, by linarith⟩
    exact (disjoint_left.mp h (subset_closure (h₀ hx)) (subset_closure (h₁ hx))).elim

end PoincareConjecture.M76.Dehn.Annuli
