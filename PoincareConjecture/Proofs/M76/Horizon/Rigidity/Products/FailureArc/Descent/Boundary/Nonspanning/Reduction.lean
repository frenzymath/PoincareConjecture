import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Selection.Tube
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Selection.Map
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Selection.Ordinary
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Selection.Essentiality
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Boundary.Proper
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Retention.Count



set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip
open PoincareConjecture.M76 PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.Annuli
open PolygonalCrossingResolution

namespace Geometry.OriginalPLTower.OrdinaryMarkedPlanarAnnulus

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "T" => spanningOuterSquare
local notation "D" => spanningInnerSquare

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M (Fin 3 → ℝ)}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s : Stage e S f r C} {R : Set M} {F : Bool → Set M}

theorem exists_boundary_reduction_of_outer_nonspanning_component
    (A : OrdinaryMarkedPlanarAnnulus s R F) (he : PLDomain e R)
    (hF : ∀ b, F b ⊆ frontier R)
    (hopen : ∀ b, IsOpen ((Subtype.val : frontier R → M) ⁻¹' F b))
    (hdis : Disjoint (F false) (F true))
    (K : SourceDoubleComponents s.charts A.map (T \ interior D)
      (frontier T ∪ frontier D) (s.projection ⁻¹' R))
    (i : K.Index) (hmeet : (K.pieces i ∩ frontier T).Nonempty)
    (havoid : Disjoint (K.pieces i) (frontier D)) :
    ∃ B : OrdinaryMarkedPlanarAnnulus s R F, B.boundaryCount < A.boundaryCount := by
  have hsource : T \ interior D = Ann := spanning_squares_source
  have hf : PolyhedralPLInCharts s.charts A.map (T \ interior D) := hsource.symm ▸ A.piecewiseAffine
  have hin : MapsTo A.map (T \ interior D) (s.projection ⁻¹' R) := hsource.symm ▸ A.region
  have hfront : ∀ x ∈ T \ interior D,
      A.map x ∈ frontier (s.projection ⁻¹' R) ↔ x ∈ frontier T ∪ frontier D := by
    simpa only [hsource, spanning_squares_rim] using A.proper
  obtain ⟨c, τ, hcs, hcd, havoidD, hcQ, hτ, hτi, hτR, hval, hfull,
    hcenter, hτfront, hτmark⟩ := A.exists_outer_nonspanning_tube he hF hopen hdis K i hmeet havoid
  obtain ⟨E⟩ := nonempty_nonspanningStripExteriors spanningOuterSquare_ball
    spanningInnerSquare_ball spanning_squares_nested c (fun b ↦ (hcs b).1)
      (fun b ↦ (hcs b).2.1) (fun b x hx ↦ ((hcs b).2.2 hx).1) hcQ hcd havoidD
  have h0 := fun p hp ↦ hval false p hp
  have h1 := fun p hp ↦ hval true p hp
  obtain ⟨N, g, hg, hkeep, _⟩ := E.exists_original_annulus s.compatible
    spanningInnerSquare_ball hcd hf hτ h0 h1
  have hgR := E.preserves_region N hin hτR hkeep
  have hproper := E.preserves_properness N spanningInnerSquare_ball hcQ hcd hfront hτfront hkeep
  have hmarks := E.preserves_marks N (fun b ↦ s.projection ⁻¹' F b)
    spanningInnerSquare_ball hcQ hcd
    (fun x hx hq ↦ A.mark_of_depth false ⟨x, hsource ▸ hx⟩ ((spanning_outer_frontier x).mp hq))
    (fun x hx hq ↦ A.mark_of_depth true ⟨x, hsource ▸ hx⟩ ((spanning_inner_frontier x).mp hq))
    hτmark hkeep
  let original : C(Ann, R) :=
    ⟨fun x ↦ ⟨s.projection (g x), hgR x.property⟩,
      (s.projection.continuous.comp hg.continuousOn.domRestrict).subtype_mk _⟩
  have horiginal (x : Ann) : (original x : M) = s.projection (g x) := rfl
  have hess := E.original_rims_nonnull N s.projection A.original original A.original_eq
    horiginal hkeep (A.essential true)
  obtain ⟨hcompact, hunique, hraw, _⟩ := E.preserves_ordinary_crossings N
    spanningOuterSquare_ball.isCompact spanningInnerSquare_ball K hf.continuousOn hg.continuousOn
      (fun b ↦ (hcs b).1.continuousOn) (fun b ↦ (hcs b).2.1) (fun b ↦ (hcs b).2.2)
      hcd hτi h0 h1 hfull hkeep
  have hcount := E.boundary_count_decrease N spanningInnerSquare_ball K hfront
    (fun b ↦ (hcs b).2.1) (fun b ↦ (hcs b).2.2) hcd hτi h0 h1 hfull
    (fun b ↦ if b then K.mate i else i) hcenter
    (hmeet.mono (inter_subset_inter_right _ subset_union_left)) hproper hkeep
  have hgmark (b : Bool) (z : AddCircle (4 * (8 : ℝ))) :
      s.projection (g (annulusRimPoint b z)) ∈ F b := by
    cases b
    · exact hmarks.1 _ (annulusRimPoint false z).property (by simpa using depth_annulusRimPoint false z)
    · exact hmarks.2 _ (annulusRimPoint true z).property (by simpa using depth_annulusRimPoint true z)
  let B : OrdinaryMarkedPlanarAnnulus s R F :=
    ⟨g, original, horiginal, hg, hproper, hgmark, hess, hcompact, hraw, hunique⟩
  refine ⟨B, ?_⟩
  simpa only [boundaryCount, B, hsource, spanning_squares_rim] using hcount.1

end Geometry.OriginalPLTower.OrdinaryMarkedPlanarAnnulus
