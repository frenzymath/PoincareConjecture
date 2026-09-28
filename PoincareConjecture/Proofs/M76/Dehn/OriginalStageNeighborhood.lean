import PoincareConjecture.Proofs.M76.Dehn.OriginalPLStage
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.IntrinsicImageDeformation
import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralImageRelativeDeformationNeighborhood











set_option autoImplicit false

open Set Geometry unitInterval

namespace Geometry.OriginalPLTower

variable {U E M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [FiniteDimensional ℝ U] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C R : Set M}





theorem Stage.exists_compact_relative_neighborhood
    (s : Stage e S f r C) (hS : S.faces.Finite)
    (hfR : MapsTo f S.space R) (hR : IsClosed R)
    (hr : Continuous r)
    (hrPL : ∀ i, LocallyPiecewiseAffineOn (r ∘ (e i).symm) (e i).target)
    (hcut : ∀ x ∈ C, x ∈ R ↔ 0 ≤ r x)
    (hzero : ∀ x ∈ C, x ∈ frontier R ↔ r x = 0)
    (hboundary : ∀ x ∈ frontier R,
      ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph M E),
        ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
        (∀ i, (e i).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
        ∀ y ∈ B.source, y ∈ R ↔ 0 ≤ ell (B y)) :
    ∃ (z : s.Carrier → ℝ) (t : ℝ), t ∈ Ioo (1 / 3 : ℝ) (2 / 3 : ℝ) ∧
      Continuous z ∧ (∀ x ∈ s.sourceMap '' S.space, z x = 1) ∧
      let P : Set s.Carrier := {x | t ≤ z x}
      let N : Set s.Carrier := {x | s.projection x ∈ R ∧ t ≤ z x}
      IsCompact P ∧ IsCompact N ∧ s.sourceMap '' S.space ⊆ interior P ∧
        s.sourceMap '' S.space ⊆ N ∧
        (∃ (a : C(N, N))
          (H : (ContinuousMap.id N).HomotopyRel a
            (Subtype.val ⁻¹' (s.sourceMap '' S.space))),
          range a = Subtype.val ⁻¹' (s.sourceMap '' S.space) ∧
          ∀ (tau : I) (x : N), (x : s.Carrier) ∈ frontier (s.projection ⁻¹' R) →
            (H (tau, x) : s.Carrier) ∈ frontier (s.projection ⁻¹' R)) ∧
        (∀ x ∈ frontier N,
          ∃ (ell : E →ᴬ[ℝ] ℝ) (v : E) (B : OpenPartialHomeomorph s.Carrier E),
            ell.contLinear v = 1 ∧ x ∈ B.source ∧ ell (B x) = 0 ∧
            (∀ k, (s.charts k).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
            ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ ell (B y)) ∧
        ∀ x ∈ frontier (s.projection ⁻¹' R), z x = t →
          ∃ (ell eta : E →ᴬ[ℝ] ℝ) (u v : E) (B : OpenPartialHomeomorph s.Carrier E),
            ell.contLinear u = 1 ∧ ell.contLinear v = 0 ∧ eta.contLinear v = 1 ∧
            x ∈ B.source ∧ ell (B x) = 0 ∧ eta (B x) = 0 ∧
            (∀ k, (s.charts k).symm.trans B ∈ piecewiseAffineGroupoid E) ∧
            (∀ y ∈ B.source, y ∈ N ↔ 0 ≤ ell (B y)) ∧
            (∀ y ∈ B.source,
              (y ∈ frontier (s.projection ⁻¹' R) ∧ t ≤ z y) ↔
                (ell (B y) = 0 ∧ 0 ≤ eta (B y))) ∧
            ∀ y ∈ B.source,
              (z y = t ∧ s.projection y ∈ R) ↔ (ell (B y) = 0 ∧ eta (B y) ≤ 0) := by
  have hsourceR : MapsTo s.sourceMap S.space (s.projection ⁻¹' R) := by
    intro x hx
    change s.projection (s.sourceMap x) ∈ R
    rw [s.source_eq x hx]
    exact hfR hx
  have hcut' (x : s.Carrier) (_ : x ∈ (univ : Set s.Carrier)) :
      x ∈ s.projection ⁻¹' R ↔ 0 ≤ (r ∘ s.projection) x :=
    hcut (s.projection x) (s.projection_mem x)
  have hzero' (x : s.Carrier) (_ : x ∈ (univ : Set s.Carrier)) :
      x ∈ frontier (s.projection ⁻¹' R) ↔ (r ∘ s.projection) x = 0 := by
    rw [s.frontier_region R]
    exact hzero (s.projection x) (s.projection_mem x)
  obtain ⟨z, t, ht, hz, hzA, hP, hN, hAP, hAN, _, hT, hfront, hcorner⟩ :=
    OpenPartialHomeomorph.exists_polyhedral_image_relative_deformation_neighborhood
      s.charts s.compatible s.cover S hS s.sourcePL
      isOpen_univ (fun _ _ => mem_univ _) hsourceR (hR.preimage s.projection.continuous)
      (hr.comp s.projection.continuous) (s.cutPL hrPL) hcut' hzero'
      (s.halfspace_boundary hboundary)
  obtain ⟨T, hTN, hT0, hT1, hfix, hTzero⟩ := hT
  obtain ⟨a, H, hHT, ha⟩ :=
    ContinuousMap.exists_intrinsic_image_homotopy T hTN hT0 hT1 hfix
  refine ⟨z, t, ht, hz, hzA, hP, hN, hAP, hAN, ⟨a, H, ha, ?_⟩, hfront, hcorner⟩
  intro tau x hx
  rw [hHT (tau, x)]
  exact hTzero tau x hx

end Geometry.OriginalPLTower
