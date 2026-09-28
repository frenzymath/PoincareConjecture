import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.Reparametrization.Reflection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Spanning.Canonical
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Boundary.Reparametrization.Intersection

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_planar_annulus_reflection_map :
    ∃ (H : Ann ≃ₜ Ann) (r : P2 → P2),
      FinitePiecewiseAffineOn r Ann ∧ MapsTo r Ann Ann ∧ InjOn r Ann ∧
      (∀ x : Ann, r x = (H x : P2)) ∧
      (∀ x ∈ Ann, r (r x) = x) ∧
      (∀ x ∈ Ann, depth 8 (r x) = -depth 8 x) ∧
      (∀ x ∈ Ann, r x ∈ frontier Ann ↔ x ∈ frontier Ann) := by
  obtain ⟨H, hH, hinv, hdepth, _⟩ := exists_planar_annulus_depth_reflection
  obtain ⟨r, hr, hrv⟩ := hH
  have hmap : MapsTo r Ann Ann := fun x hx ↦ (hrv ⟨x, hx⟩) ▸ (H ⟨x, hx⟩).property
  have hri : InjOn r Ann := by
    intro x hx y hy hxy
    apply congrArg Subtype.val (H.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) ?_)
    exact Subtype.ext ((hrv ⟨x, hx⟩).trans (hxy.trans (hrv ⟨y, hy⟩).symm))
  have hd (x : P2) (hx : x ∈ Ann) : depth 8 (r x) = -depth 8 x := by
    rw [← hrv ⟨x, hx⟩]
    exact hdepth ⟨x, hx⟩
  refine ⟨H, r, hr, hmap, hri, fun x ↦ (hrv x).symm, ?_, hd, ?_⟩
  · intro x hx
    have h := hrv (H ⟨x, hx⟩)
    rw [hinv] at h
    exact ((congrArg r (hrv ⟨x, hx⟩)).symm.trans h.symm)
  · intro x hx
    rw [mem_frontier_planar_annulus_iff, mem_frontier_planar_annulus_iff, hd x hx]
    constructor
    · rintro (h | h)
      · right; linarith
      · left; linarith
    · rintro (h | h)
      · right; linarith
      · left; linarith

theorem originalPL_planar_annulus_precomposition
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : P2 → X} {r : P2 → P2}
    (hf : PolyhedralPLInCharts e f Ann) (hr : FinitePiecewiseAffineOn r Ann)
    (hmap : MapsTo r Ann Ann) : PolyhedralPLInCharts e (f ∘ r) Ann := by
  have hr' := hr
  obtain ⟨K, hK, hKs, _⟩ := hr'
  have hh := hf.comp_finitePiecewiseAffineOn K hK
    (hKs.symm ▸ hr) (fun x hx ↦ hmap (hKs.subset hx))
  exact hKs ▸ hh

end PoincareConjecture.M76.Dehn.Annuli
