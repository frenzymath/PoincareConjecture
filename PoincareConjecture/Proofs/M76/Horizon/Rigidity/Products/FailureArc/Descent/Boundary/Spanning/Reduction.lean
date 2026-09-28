import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Spanning.StateGeometry
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Spanning.OrientedTube
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Spanning.MarkedEnds
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Spanning.Construction



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

theorem exists_boundary_reduction_of_spanning_component
    (A : OrdinaryMarkedPlanarAnnulus s R F) (he : PLDomain e R)
    (hF : ∀ b, F b ⊆ frontier R)
    (hopen : ∀ b, IsOpen ((Subtype.val : frontier R → M) ⁻¹' F b))
    (hdis : Disjoint (F false) (F true))
    (K : SourceDoubleComponents s.charts A.map (T \ interior D)
      (frontier T ∪ frontier D) (s.projection ⁻¹' R))
    (i : K.Index) (hmeet0 : (K.pieces i ∩ frontier T).Nonempty)
    (hmeet1 : (K.pieces i ∩ frontier D).Nonempty) :
    ∃ B : OrdinaryMarkedPlanarAnnulus s R F, B.boundaryCount < A.boundaryCount := by
  let Q (b : Bool) := if b then frontier D else frontier T
  let mark (b : Bool) := s.projection ⁻¹' F b
  have hsource : T \ interior D = Ann := spanning_squares_source
  have hf : PolyhedralPLInCharts s.charts A.map (T \ interior D) := hsource.symm ▸ A.piecewiseAffine
  have hin : MapsTo A.map (T \ interior D) (s.projection ⁻¹' R) := hsource.symm ▸ A.region
  have hfront : ∀ x ∈ T \ interior D,
      A.map x ∈ frontier (s.projection ⁻¹' R) ↔ x ∈ frontier T ∪ frontier D := by
    simpa only [hsource, spanning_squares_rim] using A.proper
  have hmark (b : Bool) : MapsTo A.map ((T \ interior D) ∩ Q b) (mark b) := by
    intro x hx
    apply A.mark_of_depth b ⟨x, hsource ▸ hx.1⟩
    cases b
    · exact (spanning_outer_frontier x).mp hx.2
    · exact (spanning_inner_frontier x).mp hx.2
  have hmarkdis : Disjoint (mark false) (mark true) := hdis.preimage s.projection
  obtain ⟨W, hW, hAW, htrace⟩ := A.exists_original_mark_neighborhood hF hopen
  have hKW : A.map '' K.pieces i ⊆ s.projection ⁻¹' W := by
    rintro x ⟨z, hz, rfl⟩
    have hz' : z ∈ doubleLocusOn A.map (T \ interior D) := K.space ▸ K.pieces_subset i hz
    exact hAW (hsource ▸ hz'.1)
  obtain ⟨c, τ, hcs, hcd, hτ, hτi, hτR, hτW, hval, hfull, hcenter,
    hτfront, houter, hinner⟩ := K.exists_oriented_spanning_tube Q mark hf
      (s.plDomain_region he) i (fun b ↦ by cases b <;> exact isClosed_frontier)
        spanning_squares_disjoint hmarkdis hmark hin hfront hmeet0 hmeet1
          (hW.preimage s.projection.continuous) hKW
  have hprojfront : ∀ z ∈ tube, s.projection (τ z) ∈ frontier R ↔ z.2 = 0 ∨ z.2 = 1 := by
    simpa only [s.frontier_region, mem_preimage] using hτfront
  have hτcont : ContinuousOn (s.projection ∘ τ) tube :=
    s.projection.continuous.comp_continuousOn hτ.continuousOn
  have hbottomcenter : s.projection (τ ((0, 0), 0)) ∈ F false := by
    have hz : ((0, 0) : P2) ∈ source := by norm_num [source]
    have hh := hmark false ⟨(hcs false).2.2 hz, (houter false _ hz).mpr rfl⟩
    simpa [mark, hval false _ hz, originalStripSheet] using hh
  have htopcenter : s.projection (τ ((0, 0), 1)) ∈ F true := by
    have hz : ((1, 0) : P2) ∈ source := by norm_num [source]
    have hh := hmark true ⟨(hcs false).2.2 hz, (hinner false _ hz).mpr rfl⟩
    simpa [mark, hval false _ hz, originalStripSheet] using hh
  have hbottom : ∀ z ∈ tube, z.2 = 0 → τ z ∈ mark false :=
    tube_end_mapsTo_original_mark F hopen hdis (s.projection ∘ τ) hτcont hτW
      htrace.subset hprojfront false 0 (Or.inl rfl) hbottomcenter
  have htop : ∀ z ∈ tube, z.2 = 1 → τ z ∈ mark true :=
    tube_end_mapsTo_original_mark F hopen hdis (s.projection ∘ τ) hτcont hτW
      htrace.subset hprojfront true 1 (Or.inr rfl) htopcenter
  obtain ⟨rim, hrim, hnon⟩ := A.exists_canonical_original_rim
  obtain ⟨g, original, hg, hv, _, hproper, hg0, hg1, hess, _, hc, hraw, hu, _, hcount, _⟩ :=
    exists_essential_ordinary_spanning_surgery s.compatible spanningInnerSquare_ball
      spanningOuterSquare_ball spanning_squares_nested c (fun b ↦ (hcs b).1)
      (fun b ↦ (hcs b).2.1) (fun b ↦ (hcs b).2.2) houter hinner hcd hf hτ hτi
      (fun p hp ↦ hval false p hp) (fun p hp ↦ hval true p hp) hfull mark hin hτR
      hfront hτfront (fun x hx hq ↦ hmark false ⟨hx, hq⟩)
      (fun x hx hq ↦ hmark true ⟨hx, hq⟩) hbottom htop K
      (fun b ↦ if b then K.mate i else i) hcenter s.projection (fun _ hx ↦ hx) rim hrim hnon
  have hgmark (b : Bool) (z : AddCircle (4 * (8 : ℝ))) :
      s.projection (g (annulusRimPoint b z)) ∈ F b := by
    cases b
    · exact hg0 _ (annulusRimPoint false z).property (by simpa using depth_annulusRimPoint false z)
    · exact hg1 _ (annulusRimPoint true z).property (by simpa using depth_annulusRimPoint true z)
  let B : OrdinaryMarkedPlanarAnnulus s R F :=
    ⟨g, original, hv, hg, hproper, hgmark, hess, hc, hraw, hu⟩
  refine ⟨B, ?_⟩
  simpa only [boundaryCount, B, hsource, spanning_squares_rim] using hcount

end Geometry.OriginalPLTower.OrdinaryMarkedPlanarAnnulus
