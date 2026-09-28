import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.RegularCarrier
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.AnnulusHeight
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Relation.SourceCarriers







set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76
local notation "V2" => (ℝ × ℝ)
local notation "V3" => (Fin 3 → ℝ)

theorem exists_regular_planar_annulus_intersection_collar
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3)
    (Source K : SimplicialComplex ℝ V2) (hSource : Source.faces.Finite) (hK : K.faces.Finite)
    (hKs : K.space = squareAnnulus 8 1)
    {f g : V2 → X} (hf : PolyhedralPLInCharts e f Source.space)
    (hg : PolyhedralPLInCharts e g K.space) (hfi : InjOn f Source.space) (hgi : InjOn g K.space)
    (hboundary : ∀ x ∈ frontier (squareAnnulus 8 1), g x ∈ f '' Source.space →
      Nonempty (OriginalSurfacePairChart e (f '' Source.space) (g '' K.space) (g x) true))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (c : ℝ) (R M P : SimplicialComplex ℝ V2),
      0 < c ∧ c < δ ∧ R.faces.Finite ∧ R.IsSubdivision K ∧
      R.space = squareAnnulus 8 1 ∧ M ≤ R ∧ M.faces.Finite ∧
      M.space = squareAnnulus 8 1 ∩ {x | planarAnnulusRimHeight x ≤ c} ∧
      frontier (squareAnnulus 8 1) ⊆ M.space ∧
      (∀ s ∈ R.faces, (∀ v ∈ s, v ∈ M.vertices) → s ∈ M.faces) ∧
      P.faces.Finite ∧ (∀ s ∈ P.faces, s.card ≤ 2) ∧
      P.AffineOnFaces planarAnnulusRimHeight ∧
      (∀ v ∈ P.vertices, planarAnnulusRimHeight v ≠ c) ∧
      {x | x ∈ squareAnnulus 8 1 ∧ g x ∈ f '' Source.space ∧ planarAnnulusRimHeight x = c}.Finite ∧
      ({x | x ∈ squareAnnulus 8 1 ∧ g x ∈ f '' Source.space ∧ planarAnnulusRimHeight x = c} =
        P.space ∩ {x | planarAnnulusRimHeight x = c}) ∧
      ∀ x ∈ squareAnnulus 8 1, g x ∈ f '' Source.space → planarAnnulusRimHeight x = c →
        ∃ s ∈ P.faces, s.card = 2 ∧ x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set V2)) := by
  obtain ⟨_, G, _, _, hG, _, hGs, _⟩ :=
    hf.exists_paired_intersection_source_carriers he Source K hSource hK hg hfi hgi
  have hcompact : IsCompact (squareAnnulus 8 1) := hKs ▸ K.isCompact_space_of_finite hK
  have hrimK : frontier (squareAnnulus 8 1) ⊆ K.space :=
    frontier_subset_closure.trans (hcompact.isClosed.closure_eq.subset.trans hKs.symm.subset)
  have hrim : IsCompact (frontier (squareAnnulus 8 1)) :=
    hcompact.of_isClosed_subset isClosed_frontier (hrimK.trans hKs.subset)
  obtain ⟨c, R, M, P, hc, hcδ, hR, hRK, hRs, hMR, hM, hMs, hrimM, hfull,
      hP, hPc, hPz, hreg, hfinite, hlevel, hpoints⟩ :=
    exists_regular_boundary_intersection_subcomplex K G hK hG hg hgi
      (f '' Source.space) (frontier (squareAnnulus 8 1)) hrim hrimK hGs
      (fun x hx => hboundary x hx.2 (hGs.subset hx.1).2)
      (finitePiecewiseAffineOn_planarAnnulusRimHeight K hK)
      (fun x hx => planarAnnulusRimHeight_nonneg (hKs.subset hx))
      (fun x hx => planarAnnulusRimHeight_eq_zero_iff (hKs.subset hx)) hδ
  have heq : {x | x ∈ squareAnnulus 8 1 ∧ g x ∈ f '' Source.space ∧ planarAnnulusRimHeight x = c} =
      G.space ∩ {x | planarAnnulusRimHeight x = c} := by
    rw [hGs, hKs]
    ext x
    exact and_assoc.symm
  refine ⟨c, R, M, P, hc, hcδ, hR, hRK, hRs.trans hKs, hMR, hM,
    by simpa only [hKs] using hMs, hrimM, hfull, hP, hPc, hPz, hreg,
    heq.symm ▸ hfinite, heq.trans hlevel, ?_⟩
  intro x hx hxf hxc
  exact hpoints x (heq.subset ⟨hx, hxf, hxc⟩)

end PoincareConjecture.M76
