import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.BoundaryReduction.Minimal
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Annulus.BoundaryReduction.Selection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Spanning.Reduction
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Reduction



set_option autoImplicit false
open Set Geometry Topology PLAnnularStrip
open PoincareConjecture.M76 PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.Annuli

namespace Geometry.OriginalPLTower.OrdinaryMarkedPlanarAnnulus

local notation "T" => spanningOuterSquare
local notation "D" => spanningInnerSquare

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M (Fin 3 → ℝ)}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s : Stage e S f r C} {R : Set M} {F : Bool → Set M}

theorem exists_boundary_reduction_of_outer_component
    (A : OrdinaryMarkedPlanarAnnulus s R F) (he : PLDomain e R)
    (hF : ∀ b, F b ⊆ frontier R)
    (hopen : ∀ b, IsOpen ((Subtype.val : frontier R → M) ⁻¹' F b))
    (hdis : Disjoint (F false) (F true))
    (K : SourceDoubleComponents s.charts A.map (T \ interior D)
      (frontier T ∪ frontier D) (s.projection ⁻¹' R))
    (i : K.Index) (hmeet : (K.pieces i ∩ frontier T).Nonempty) :
    ∃ B : OrdinaryMarkedPlanarAnnulus s R F, B.boundaryCount < A.boundaryCount := by
  classical
  by_cases hinner : (K.pieces i ∩ frontier D).Nonempty
  · exact A.exists_boundary_reduction_of_spanning_component he hF hopen hdis K i hmeet hinner
  · exact A.exists_boundary_reduction_of_outer_nonspanning_component he hF hopen hdis K i hmeet
      (disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hinner))

theorem exists_boundary_reduction
    (A : OrdinaryMarkedPlanarAnnulus s R F) (he : PLDomain e R)
    (hF : ∀ b, F b ⊆ frontier R)
    (hopen : ∀ b, IsOpen ((Subtype.val : frontier R → M) ⁻¹' F b))
    (hdis : Disjoint (F false) (F true)) (hpos : 0 < A.boundaryCount) :
    ∃ B : OrdinaryMarkedPlanarAnnulus s R F, B.boundaryCount < A.boundaryCount := by
  rcases A.exists_outer_component_or_reflected hpos with ⟨K, i, hi⟩ | ⟨B, hB, K, i, hi⟩
  · exact A.exists_boundary_reduction_of_outer_component he hF hopen hdis K i hi
  · obtain ⟨E, hE⟩ := B.exists_boundary_reduction_of_outer_component he
      (fun b ↦ hF (!b)) (fun b ↦ hopen (!b)) (by simpa using hdis.symm) K i hi
    obtain ⟨_, B', _, _, _, _, _, hB', _⟩ := E.exists_depth_reflection
    have hh : ∃ V : OrdinaryMarkedPlanarAnnulus s R (fun b ↦ F (!(!b))),
        V.boundaryCount < A.boundaryCount := by
      refine ⟨B', ?_⟩
      rw [hB']
      exact hE.trans_eq hB
    have hmarks : (fun b ↦ F (!(!b))) = F := by
      funext b
      cases b <;> rfl
    rw [hmarks] at hh
    exact hh

theorem exists_boundary_count_zero
    (A : OrdinaryMarkedPlanarAnnulus s R F) (he : PLDomain e R)
    (hF : ∀ b, F b ⊆ frontier R)
    (hopen : ∀ b, IsOpen ((Subtype.val : frontier R → M) ⁻¹' F b))
    (hdis : Disjoint (F false) (F true)) :
    ∃ B : OrdinaryMarkedPlanarAnnulus s R F, B.boundaryCount = 0 := by
  obtain ⟨B, hminimal⟩ := A.exists_minimal_boundary_count
  refine ⟨B, ?_⟩
  by_contra hzero
  obtain ⟨V, hV⟩ := B.exists_boundary_reduction he hF hopen hdis (Nat.pos_of_ne_zero hzero)
  exact (Nat.not_lt_of_ge (hminimal V)) hV

theorem nonempty_embedded
    (A : OrdinaryMarkedPlanarAnnulus s R F) (he : PLDomain e R)
    (hF : ∀ b, F b ⊆ frontier R)
    (hopen : ∀ b, IsOpen ((Subtype.val : frontier R → M) ⁻¹' F b))
    (hdis : Disjoint (F false) (F true)) :
    Nonempty (MarkedEssentialPlanarAnnulus s R F) := by
  obtain ⟨B, hB⟩ := A.exists_boundary_count_zero he hF hopen hdis
  exact B.nonempty_embedded_of_boundaryCount_zero he hB

end Geometry.OriginalPLTower.OrdinaryMarkedPlanarAnnulus
