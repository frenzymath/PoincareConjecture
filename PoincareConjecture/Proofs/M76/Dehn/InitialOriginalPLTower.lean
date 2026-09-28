import PoincareConjecture.Proofs.M76.Dehn.OriginalPLStage
import PoincareConjecture.Proofs.M76.Dehn.OriginalBoundaryDefiningCut
import PoincareConjecture.Proofs.M76.Mathlib.CompactPLNeighborhoodModel

set_option autoImplicit false

open Set Topology Geometry

namespace Geometry.OriginalPLTower

variable {U E M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [FiniteDimensional ℝ U] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [T2Space M]
  [LocallyCompactSpace M]

theorem exists_original_graph_stage
    (e : ι → OpenPartialHomeomorph M E)
    (hcompat : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid E)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (S : SimplicialComplex ℝ U) (hS : S.faces.Finite)
    [PathConnectedSpace S.space]
    {f : U → M} (hf : PolyhedralPLInCharts e f S.space) (v0 : S.space)
    {R : Set M} (hfR : MapsTo f S.space R)
    (hboundary : ∀ x ∈ frontier R,
      ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph M E),
        ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) :
    ∃ (r : M → ℝ) (W : Set M) (s : Finset (f '' S.space))
      (q : M → (s → ℝ × E)) (C : Set M) (t : Stage e S f r C),
      IsOpen W ∧ IsCompact C ∧ f '' S.space ⊆ interior C ∧ C ⊆ W ∧
      Continuous r ∧
      (∀ i, LocallyPiecewiseAffineOn (r ∘ (e i).symm) (e i).target) ∧
      Continuous q ∧
      (∀ i, LocallyPiecewiseAffineOn (q ∘ (e i).symm) (e i).target) ∧
      InjOn q C ∧ FinitePiecewiseAffineOn (q ∘ f) S.space ∧
      IsOpenEmbedding t.projection ∧
      ∀ y ∈ W, (y ∈ R ↔ 0 ≤ r y) ∧
        (y ∈ frontier R ↔ r y = 0) ∧ (y ∈ interior R ↔ 0 < r y) := by
  have hA : IsCompact (f '' S.space) :=
    (S.isCompact_space_of_finite hS).image_of_continuousOn hf.continuousOn
  have hAR : f '' S.space ⊆ R := by
    rintro _ ⟨x, hx, rfl⟩
    exact hfR hx
  obtain ⟨r, W, hW, hAW, hr, hrPL, hcut⟩ :=
    OpenPartialHomeomorph.exists_PL_defining_cut_near_compact e hcompat hcover hA hAR
      hboundary
  obtain ⟨s, q, C, _, H, hC, hAC, hCW, _, hq, hqPL, hHq, _⟩ :=
    OpenPartialHomeomorph.exists_compact_PL_neighborhood_model e hcompat hcover hA hW hAW
  have hqinj : InjOn q C := by
    intro x hx y hy hxy
    have he : H ⟨x, hx⟩ = H ⟨y, hy⟩ := Subtype.ext
      ((hHq ⟨x, hx⟩).trans (hxy.trans (hHq ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (H.injective he)
  have hF : FinitePiecewiseAffineOn (q ∘ f) S.space :=
    hf.finitePiecewiseAffineOn_comp S hS hqPL
  obtain ⟨t, ht⟩ := exists_initial_stage hcompat hcover hS hf v0 hAC hr hrPL
  exact ⟨r, W, s, q, C, t, hW, hC, hAC, hCW, hr, hrPL,
    hq, hqPL, hqinj, hF, ht, hcut⟩

end Geometry.OriginalPLTower
