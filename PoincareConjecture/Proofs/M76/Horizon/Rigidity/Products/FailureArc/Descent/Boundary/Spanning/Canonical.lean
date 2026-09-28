import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.Ordinary
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Pasting.SourceCopies

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

noncomputable def spanningInnerSquare : Set (ℝ × ℝ) := Dehn.annulusSquare 8 1
noncomputable def spanningOuterSquare : Set (ℝ × ℝ) := Dehn.annulusSquare 8 (-1)

theorem spanningInnerSquare_ball : IsFinitePLBallPair (ℝ × ℝ)
    spanningInnerSquare (frontier spanningInnerSquare) :=
  Dehn.isFinitePLBallPair_annulusSquare (by norm_num)

theorem spanningOuterSquare_ball : IsFinitePLBallPair (ℝ × ℝ)
    spanningOuterSquare (frontier spanningOuterSquare) :=
  Dehn.isFinitePLBallPair_annulusSquare (by norm_num)

theorem spanning_squares_nested : spanningInnerSquare ⊆ interior spanningOuterSquare := by
  intro z hz
  have hh := (Dehn.mem_annulusSquare_iff 8 1 z).mp hz
  apply (Dehn.mem_interior_annulusSquare_iff 8 (-1) z).mpr
  linarith

theorem spanning_squares_source : spanningOuterSquare \ interior spanningInnerSquare =
    squareAnnulus 8 1 := by
  ext z
  rw [spanningOuterSquare, spanningInnerSquare, mem_sdiff, Dehn.mem_annulusSquare_iff, Dehn.mem_interior_annulusSquare_iff,
    mem_squareAnnulus_iff_depth, mem_Icc]
  exact and_congr_right (fun _ ↦ not_lt)

theorem spanning_outer_frontier (z : ℝ × ℝ) :
    z ∈ frontier spanningOuterSquare ↔ depth 8 z = -1 :=
  Dehn.mem_frontier_annulusSquare_iff 8 (-1) z

theorem spanning_inner_frontier (z : ℝ × ℝ) :
    z ∈ frontier spanningInnerSquare ↔ depth 8 z = 1 :=
  Dehn.mem_frontier_annulusSquare_iff 8 1 z

theorem spanning_squares_rim : frontier spanningOuterSquare ∪ frontier spanningInnerSquare =
    {z : ℝ × ℝ | depth 8 z = -1 ∨ depth 8 z = 1} := by
  ext z
  simp only [mem_union, spanning_outer_frontier, spanning_inner_frontier, mem_ofPred_eq]

theorem spanning_squares_disjoint :
    Disjoint (frontier spanningOuterSquare) (frontier spanningInnerSquare) := by
  apply disjoint_left.mpr
  intro z h₀ h₁
  have h₀ := (spanning_outer_frontier z).mp h₀
  have h₁ := (spanning_inner_frontier z).mp h₁
  linarith

end PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower.OrdinaryMarkedPlanarAnnulus

open PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.Annuli

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M (Fin 3 → ℝ)}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s : Stage e S f r C} {R : Set M} {F : Bool → Set M}

theorem nonempty_canonical_components (A : OrdinaryMarkedPlanarAnnulus s R F) :
    Nonempty (SourceDoubleComponents s.charts A.map
      (spanningOuterSquare \ interior spanningInnerSquare)
      (frontier spanningOuterSquare ∪ frontier spanningInnerSquare) (s.projection ⁻¹' R)) := by
  simpa only [spanning_squares_source, spanning_squares_rim] using A.nonempty_components

end Geometry.OriginalPLTower.OrdinaryMarkedPlanarAnnulus
