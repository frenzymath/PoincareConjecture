import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Spanning.Canonical
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.MarkedFrontierNeighborhood



set_option autoImplicit false
open Set Geometry PLAnnularStrip
open PoincareConjecture.M76 PoincareConjecture.M76.Dehn PoincareConjecture.M76.Dehn.Annuli

namespace Geometry.OriginalPLTower.OrdinaryMarkedPlanarAnnulus

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Rim" => Set.ofPred (fun x : P2 ↦ depth 8 x = -1 ∨ depth 8 x = 1)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M (Fin 3 → ℝ)}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s : Stage e S f r C} {R : Set M} {F : Bool → Set M}
  (A : OrdinaryMarkedPlanarAnnulus s R F)

theorem mark_of_depth (b : Bool) (x : Ann)
    (hx : depth 8 (x : P2) = if b then 1 else -1) :
    s.projection (A.map x) ∈ F b := by
  have hr : x ∈ Set.range (annulusRimPoint b) := by
    rw [range_annulusRimPoint]
    exact hx
  obtain ⟨z, rfl⟩ := hr
  exact A.mark b z

theorem exists_canonical_original_rim :
    ∃ rim : C(frontier spanningOuterSquare, R),
      (∀ z : frontier spanningOuterSquare, (rim z : M) = s.projection (A.map z)) ∧
      ¬ rim.Nullhomotopic := by
  have hmem (z : frontier spanningOuterSquare) : (z : P2) ∈ Ann := by
    rw [mem_squareAnnulus_iff_depth, mem_Icc, (spanning_outer_frontier z).mp z.property]
    norm_num
  let inclusion : C(frontier spanningOuterSquare, Ann) :=
    ⟨fun z ↦ ⟨z, hmem z⟩, continuous_subtype_val.subtype_mk _⟩
  let rim := A.original.comp inclusion
  refine ⟨rim, fun z ↦ A.original_eq (inclusion z), ?_⟩
  intro hn
  let q : C(AddCircle (4 * (8 : ℝ)), frontier spanningOuterSquare) :=
    ⟨fun z ↦ ⟨annulusRimPoint false z, (spanning_outer_frontier _).mpr
      (by simpa using depth_annulusRimPoint false z)⟩,
      (continuous_subtype_val.comp (continuous_annulusRimPoint false)).subtype_mk _⟩
  have hv : rim.comp q = planarAnnulusRim A.original false := by
    ext z
    rfl
  exact A.essential false (hv ▸ hn.comp_left q)

theorem exists_original_mark_neighborhood
    (hF : ∀ b, F b ⊆ frontier R)
    (hopen : ∀ b, IsOpen ((Subtype.val : frontier R → M) ⁻¹' F b)) :
    ∃ W : Set M, IsOpen W ∧ MapsTo (s.projection ∘ A.map) Ann W ∧
      W ∩ frontier R = F false ∪ F true := by
  refine exists_open_neighborhood_of_proper_marked_map (B := Rim)
    (f := s.projection ∘ A.map)
    (union_subset (hF false) (hF true)) ((hopen false).union (hopen true)) A.region ?_ ?_
  · intro x hx
    simpa only [s.frontier_region, mem_preimage, Function.comp_apply] using A.proper x hx
  · intro x hx
    have hmem : x ∈ Ann := by
      rw [mem_squareAnnulus_iff_depth, mem_Icc]
      rcases hx with hx | hx <;> rw [hx] <;> norm_num
    rcases hx with hx | hx
    · exact Or.inl (A.mark_of_depth false ⟨x, hmem⟩ hx)
    · exact Or.inr (A.mark_of_depth true ⟨x, hmem⟩ hx)

end Geometry.OriginalPLTower.OrdinaryMarkedPlanarAnnulus
