import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Spanning.Canonical
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.Reparametrization.Ordinary

set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip
open PoincareConjecture.M76 PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.Annuli

namespace Geometry.OriginalPLTower.OrdinaryMarkedPlanarAnnulus

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "T" => spanningOuterSquare
local notation "D" => spanningInnerSquare

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M (Fin 3 → ℝ)}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s : Stage e S f r C} {R : Set M} {F : Bool → Set M}

theorem exists_reflected_outer_component (A : OrdinaryMarkedPlanarAnnulus s R F)
    (K : SourceDoubleComponents s.charts A.map (T \ interior D)
      (frontier T ∪ frontier D) (s.projection ⁻¹' R))
    (i : K.Index) (hmeet : (K.pieces i ∩ frontier D).Nonempty) :
    ∃ B : OrdinaryMarkedPlanarAnnulus s R (fun b ↦ F (!b)),
      B.boundaryCount = A.boundaryCount ∧
      ∃ L : SourceDoubleComponents s.charts B.map (T \ interior D)
          (frontier T ∪ frontier D) (s.projection ⁻¹' R),
        ∃ j : L.Index, (L.pieces j ∩ frontier T).Nonempty := by
  obtain ⟨H, B, _, hinv, hdepth, hval, _, hcount, _⟩ := A.exists_depth_reflection
  obtain ⟨x, hxi, hxrim⟩ := hmeet
  have hxdouble : x ∈ doubleLocusOn A.map (T \ interior D) :=
    K.space ▸ K.pieces_subset i hxi
  obtain ⟨hx, y, hy, hxy, hne⟩ := hxdouble
  let x' : Ann := ⟨x, spanning_squares_source ▸ hx⟩
  let y' : Ann := ⟨y, spanning_squares_source ▸ hy⟩
  have hBx : B.map (H x') = A.map x := by
    rw [hval, hinv]
  have hBy : B.map (H y') = A.map y := by
    rw [hval, hinv]
  have hHne : (H x' : P2) ≠ H y' := by
    intro hh
    exact hne (congrArg Subtype.val (H.injective (Subtype.ext hh)))
  have hBdouble : (H x' : P2) ∈ doubleLocusOn B.map (T \ interior D) :=
    ⟨spanning_squares_source.symm ▸ (H x').property, H y',
      spanning_squares_source.symm ▸ (H y').property, hBx.trans (hxy.trans hBy.symm), hHne⟩
  have hBrim : (H x' : P2) ∈ frontier T := by
    apply (spanning_outer_frontier _).mpr
    rw [hdepth]
    have hxdepth : depth 8 (x' : P2) = 1 := (spanning_inner_frontier x).mp hxrim
    rw [hxdepth]
  obtain ⟨L⟩ := B.nonempty_canonical_components
  obtain ⟨j, hj⟩ := mem_iUnion.mp (L.literal_cover.symm ▸ hBdouble)
  exact ⟨B, hcount, L, j, H x', hj, hBrim⟩

theorem exists_outer_component_or_reflected (A : OrdinaryMarkedPlanarAnnulus s R F)
    (hpos : 0 < A.boundaryCount) :
    (∃ K : SourceDoubleComponents s.charts A.map (T \ interior D)
        (frontier T ∪ frontier D) (s.projection ⁻¹' R),
      ∃ i : K.Index, (K.pieces i ∩ frontier T).Nonempty) ∨
    (∃ B : OrdinaryMarkedPlanarAnnulus s R (fun b ↦ F (!b)),
      B.boundaryCount = A.boundaryCount ∧
      ∃ K : SourceDoubleComponents s.charts B.map (T \ interior D)
          (frontier T ∪ frontier D) (s.projection ⁻¹' R),
        ∃ i : K.Index, (K.pieces i ∩ frontier T).Nonempty) := by
  obtain ⟨K⟩ := A.nonempty_canonical_components
  have hp : 0 < doubleBoundaryComponentCount A.map (T \ interior D)
      (frontier T ∪ frontier D) := by
    simpa only [spanning_squares_source, spanning_squares_rim, boundaryCount] using hpos
  obtain ⟨i, hi⟩ := K.exists_interval_of_boundary_count_pos hp
  obtain ⟨x, hxi, hxT | hxD⟩ := (K.interval_iff_meets_rim i).mp hi
  · exact Or.inl ⟨K, i, x, hxi, hxT⟩
  · exact Or.inr (A.exists_reflected_outer_component K i ⟨x, hxi, hxD⟩)

end Geometry.OriginalPLTower.OrdinaryMarkedPlanarAnnulus
