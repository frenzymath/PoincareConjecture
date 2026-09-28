import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Planar.SourceCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.TerminalCount
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SquareAnnulusBoundary

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip Topology

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

theorem exists_planar_annulus_complex :
    ∃ J : SimplicialComplex ℝ P2, J.faces.Finite ∧ J.space = Ann := by
  obtain ⟨_, H, _, hH, _, _, _⟩ :=
    ProtectedAnnulus.exists_planar_source_coordinates (S := ProtectedAnnulus.source) rfl
  obtain ⟨_, hF, _⟩ := hH
  obtain ⟨K, hK, hKS, _⟩ := hF
  exact ⟨K, hK, hKS⟩

theorem isCompact_planar_annulus : IsCompact Ann := by
  obtain ⟨J, hJ, hJS⟩ := exists_planar_annulus_complex
  exact hJS ▸ J.isCompact_space_of_finite hJ

theorem mem_frontier_planar_annulus_iff (x : P2) :
    x ∈ frontier Ann ↔ depth 8 x = -1 ∨ depth 8 x = 1 := by
  have hclosed := isCompact_planar_annulus.isClosed
  constructor
  · intro hx
    have hmem := hclosed.frontier_subset hx
    have habs := (mem_frontier_squareAnnulus_iff (by norm_num) (by norm_num) hmem).mp hx
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with hh | hh
    · exact Or.inr hh
    · exact Or.inl hh
  · intro hx
    have hmem : x ∈ Ann := mem_squareAnnulus_iff_depth.mpr (by rcases hx with h | h <;> rw [h] <;> norm_num)
    apply (mem_frontier_squareAnnulus_iff (by norm_num) (by norm_num) hmem).mpr
    rcases hx with h | h <;> rw [h] <;> norm_num

theorem annulusRimPoint_mem_frontier (b : Bool) (z : Circle) :
    (annulusRimPoint b z : P2) ∈ frontier Ann := by
  rw [mem_frontier_planar_annulus_iff, depth_annulusRimPoint]
  cases b <;> simp

theorem planar_annulus_frontier_eq_iUnion_rims :
    frontier Ann = ⋃ b : Bool, range (fun z : Circle ↦
      (annulusRimPoint b z : P2)) := by
  ext x
  constructor
  · intro hx
    have hxA := isCompact_planar_annulus.isClosed.frontier_subset hx
    rcases (mem_frontier_planar_annulus_iff x).mp hx with hn | hp
    · have hmem : (⟨x, hxA⟩ : Ann) ∈ range (annulusRimPoint false) := by
        rw [range_annulusRimPoint]
        exact hn
      obtain ⟨z, hz⟩ := hmem
      exact mem_iUnion.mpr ⟨false, z, congrArg Subtype.val hz⟩
    · have hmem : (⟨x, hxA⟩ : Ann) ∈ range (annulusRimPoint true) := by
        rw [range_annulusRimPoint]
        exact hp
      obtain ⟨z, hz⟩ := hmem
      exact mem_iUnion.mpr ⟨true, z, congrArg Subtype.val hz⟩
  · intro hx
    obtain ⟨b, z, rfl⟩ := mem_iUnion.mp hx
    exact annulusRimPoint_mem_frontier b z

theorem eqOn_planar_annulus_frontier_of_rim_values {X : Type*} {f g : P2 → X}
    (h : ∀ b z, f (annulusRimPoint b z) =
      g (annulusRimPoint b z)) : EqOn f g (frontier Ann) := by
  intro x hx
  rw [planar_annulus_frontier_eq_iUnion_rims] at hx
  obtain ⟨b, z, rfl⟩ := mem_iUnion.mp hx
  exact h b z

theorem planar_annulus_collision_free_of_double_interior
    {X : Type*} [TopologicalSpace X] {f : P2 → X} {R : Set X}
    (hfront : ∀ x ∈ Ann, f x ∈ frontier R ↔ depth 8 x = -1 ∨ depth 8 x = 1)
    (hint : MapsTo f (doubleLocusOn f Ann) (interior R)) :
    Disjoint (doubleLocusOn f Ann) (frontier Ann) := by
  apply disjoint_left.mpr
  intro x hx hb
  exact disjoint_left.mp disjoint_interior_frontier (hint hx)
    ((hfront x hx.1).mpr ((mem_frontier_planar_annulus_iff x).mp hb))

theorem SourceCircleDecomposition.unique_other_points
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → X} {S : Set E} (M : SourceCircleDecomposition f S) :
    ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
      x ≠ y → x ≠ z → f x = f y → f x = f z → y = z := by
  intro x hx y hy z hz hxy hxz hfy hfz
  have hdouble : x ∈ doubleLocusOn f S := ⟨hx, y, hy, hfy, hxy⟩
  let a : M.graph.space := ⟨x, M.space.symm.subset hdouble⟩
  exact (M.unique a y hy hxy hfy).trans (M.unique a z hz hxz hfz).symm

end PoincareConjecture.M76.Dehn.Annuli
