import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.ExteriorProjectionFibers
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalPrimalSectors
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallTopology

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.OriginalTriangleCopies

theorem connected_subset_unique_closed_piece
    {X ι : Type*} [TopologicalSpace X] [Finite ι]
    {S : Set X} (hS : IsConnected S) (U : ι → Set X)
    (hclosed : ∀ i, IsClosed (U i)) (hcover : S ⊆ ⋃ i, U i)
    (havoid : ∀ i j, i ≠ j → Disjoint S (U i ∩ U j)) :
    ∃! i, S ⊆ U i := by
  classical
  obtain ⟨x, hx⟩ := hS.nonempty
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover hx)
  have hSi : S ⊆ U i := by
    intro y hy
    by_contra hyi
    let V : Set X := ⋃ j : {j : ι // j ≠ i}, U j.val
    have hV : IsClosed V := isClosed_iUnion_of_finite (fun j ↦ hclosed j.val)
    have hcover' : S ⊆ U i ∪ V := by
      intro z hz
      obtain ⟨j, hzj⟩ := mem_iUnion.mp (hcover hz)
      by_cases hji : j = i
      · exact Or.inl (hji ▸ hzj)
      · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hzj⟩)
    have hyV := (hcover' hy).resolve_left hyi
    obtain ⟨z, hzS, hzi, hzV⟩ := (isPreconnected_closed_iff.mp hS.isPreconnected)
      (U i) V (hclosed i) hV hcover' ⟨x, hx, hxi⟩ ⟨y, hy, hyV⟩
    obtain ⟨j, hzj⟩ := mem_iUnion.mp hzV
    exact Set.disjoint_left.mp (havoid i j.val j.property.symm) hzS ⟨hzi, hzj⟩
  refine ⟨i, hSi, ?_⟩
  intro j hSj
  by_contra hji
  exact Set.disjoint_left.mp (havoid j i hji) hx ⟨hSj hx, hSi hx⟩

theorem connected_image_unique_closed_piece
    {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Finite ι]
    {S : Set X} (hS : IsConnected S) {f : X → Y} (hf : ContinuousOn f S)
    (U : ι → Set Y) {q marks : Set Y} (hclosed : ∀ i, IsClosed (U i))
    (hcover : (⋃ i, U i) = q) (himage : f '' S ⊆ q)
    (hinter : ∀ i j, i ≠ j → U i ∩ U j ⊆ marks)
    (havoid : Disjoint (f '' S) marks) :
    ∃! i, f '' S ⊆ U i := by
  apply connected_subset_unique_closed_piece (hS.image f hf) U hclosed
    (himage.trans hcover.symm.subset)
  intro i j hij
  exact havoid.mono_right (hinter i j hij)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem OriginalPrimalSectorDecomposition.rim_iUnion
    {d q : Set E} {marks : Fin 4 → E} (C : OriginalPrimalSectorDecomposition d q marks) :
    (⋃ i, C.rim i) = q := by
  apply Eq.trans ?_ C.rim_cover
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    fin_cases i
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)
  · rintro ((h | h) | (h | h))
    · exact mem_iUnion.mpr ⟨0, h⟩
    · exact mem_iUnion.mpr ⟨1, h⟩
    · exact mem_iUnion.mpr ⟨2, h⟩
    · exact mem_iUnion.mpr ⟨3, h⟩

theorem OriginalPrimalSectorDecomposition.rim_inter_subset_marks
    {d q : Set E} {marks : Fin 4 → E} (C : OriginalPrimalSectorDecomposition d q marks)
    {i j : Fin 4} (hij : i ≠ j) : C.rim i ∩ C.rim j ⊆ range marks := by
  have hcases : j = i + 1 ∨ j = i + 2 ∨ i = j + 1 := by
    fin_cases i <;> fin_cases j <;> first | exact (hij rfl).elim | decide
  intro x hx
  rcases hcases with hnext | hopp | hprev
  · rw [hnext, C.rim_inter_next] at hx
    exact ⟨C.order (i + 1), (show x = marks (C.order (i + 1)) from hx).symm⟩
  · exact (Set.disjoint_left.mp (C.rim_disjoint_opposite i) hx.1 (hopp ▸ hx.2)).elim
  · have heq := (C.rim_inter_next j).subset ⟨hx.2, hprev ▸ hx.1⟩
    exact ⟨C.order (j + 1), (show x = marks (C.order (j + 1)) from heq).symm⟩

theorem OriginalPrimalSectorDecomposition.connected_image_unique_rim
    {X : Type*} [TopologicalSpace X] {d q : Set E} {marks : Fin 4 → E}
    (C : OriginalPrimalSectorDecomposition d q marks)
    {S : Set X} (hS : IsConnected S) {f : X → E} (hf : ContinuousOn f S)
    (himage : f '' S ⊆ q) (havoid : Disjoint (f '' S) (range marks)) :
    ∃! i : Fin 4, f '' S ⊆ C.rim i :=
  connected_image_unique_closed_piece hS hf C.rim
    (fun i ↦ (C.rim_ball i).isCompact.isClosed) C.rim_iUnion himage
    (fun _ _ hij ↦ C.rim_inter_subset_marks hij) havoid

open Classical PreAbstractSimplicialComplex.ModTwoCochains

variable [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype K.vertices]
  [Fintype K.barycentricSubdivision.faces]
  (P : SimpleGraph K.vertices)
  (D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
  (hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P)
  (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2)
  [Fintype (ResidualComplementaryEdge K P D)]
  (B : ∀ s : ResidualComplementaryEdge K P D,
    OriginalResidualHalfBands K (complementaryOriginalEdge K P hcofaces s.val))
  (h : ResidualHalfBandIndex K P D → E → ℝ)

noncomputable def complementaryBridgeCopies : Set (E × (ResidualHalfBandIndex K P D → ℝ)) :=
  ⋃ s : ResidualComplementaryEdge K P D, ⋃ j : Fin 2,
    separatedSheet h (s, j) '' residualBridge K (complementaryOriginalEdge K P hcofaces s.val)
      ((B s).ends 0) ((B s).ends 1)

theorem complementary_gap_projection_avoids_marks
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    {S : Set (E × (ResidualHalfBandIndex K P D → ℝ))}
    (hS : S ⊆ complementaryCutCarrier K P D hD hcofaces B h)
    (havoid : Disjoint S (complementaryBridgeCopies K P D hcofaces B h)) :
    Disjoint (Prod.fst '' S) (residualQuarterMarks K P D hcofaces B) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨p, hp, rfl⟩ hx
  obtain ⟨s, hs⟩ := mem_iUnion.mp hx
  have hbridge : p.1 ∈ residualBridge K (complementaryOriginalEdge K P hcofaces s.val)
      ((B s).ends 0) ((B s).ends 1) := by
    rcases hs with hs | hs
    · have hs' : p.1 = primalEdgeMark K (complementaryOriginalEdge K P hcofaces s.val)
        ((B s).ends 0) := hs
      rw [hs']
      exact left_mem_segment ℝ _ _
    · have hs' : p.1 = primalEdgeMark K (complementaryOriginalEdge K P hcofaces s.val)
        ((B s).ends 1) := hs
      rw [hs']
      exact right_mem_segment ℝ _ _
  have hpair := (complementaryCut_bridge_fiber K P D hD hcofaces B h hbound s hbridge).subset
    ⟨hS hp, rfl⟩
  have hcopy : p ∈ complementaryBridgeCopies K P D hcofaces B h := by
    rcases hpair with hp0 | hp1
    · exact mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨0, p.1, hbridge, hp0.symm⟩⟩
    · exact mem_iUnion.mpr ⟨s, mem_iUnion.mpr ⟨1, p.1, hbridge, hp1.symm⟩⟩
  exact Set.disjoint_left.mp havoid hp hcopy

theorem complementary_connected_gap_unique_original_rim
    (hP : P ≤ K.vertexAbstractComplex.edgeGraph)
    (hbound : ∀ t ∈ K.faces, t.card ≤ 3)
    (marks : Fin 4 → E)
    (hmarks : range marks = residualQuarterMarks K P D hcofaces B)
    (C : OriginalPrimalSectorDecomposition
      (K.barycentricSubdivision.vertexDualUnion (primalCentroidSet K P hP))
      (K.barycentricSubdivision.vertexDualRim (primalCentroidSet K P hP)) marks)
    {S : Set (E × (ResidualHalfBandIndex K P D → ℝ))}
    (hS : IsConnected S) (hcarrier : S ⊆ complementaryCutCarrier K P D hD hcofaces B h)
    (havoid : Disjoint S (complementaryBridgeCopies K P D hcofaces B h))
    (himage : Prod.fst '' S ⊆
      K.barycentricSubdivision.vertexDualRim (primalCentroidSet K P hP)) :
    ∃! i : Fin 4, Prod.fst '' S ⊆ C.rim i := by
  apply C.connected_image_unique_rim hS continuous_fst.continuousOn himage
  rw [hmarks]
  exact complementary_gap_projection_avoids_marks K P D hD hcofaces B h hbound hcarrier havoid

end PoincareConjecture.M76.OriginalTriangleCopies
